> {-# LANGUAGE DeriveFunctor #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE NoMonomorphismRestriction #-}
> {-# LANGUAGE TypeSynonymInstances #-}

This is a modern "translation" of Cousot and Cousot's original
paper on abstract interpretation (1977). I created it for myself, to
see how well I understood its ideas, but you may also find it
useful. The structure closely follows the structure of the original
paper, so it should be possible to read this translation and the
original paper in parallel. Primarily it's useful for loading
into ghci and typing `:info Foo` whenever you need to recall what
the meaning of Foo is.

> module AbstractInterpretation where
>
> import Control.Applicative
> import Control.Monad
> import Data.Monoid

Section 3.1 on page 238, Syntax of a program.

A program (flowchart) is built from a set of nodes, each with
successor and predecessor nodes.

> data Connections self neighbor = Connections {
>   nPred :: self -> [neighbor],
>   nSucc :: self -> [neighbor] }

In the original paper, both self and neighbor are of type `Node`.

> data Program node ident expr bexpr prim = Program {
>   connections :: Connections node node,
>   classify :: node -> NodeType node ident expr bexpr,
>   upcast :: bexpr -> expr,
>   entryNodes :: [Entry node],
>   val :: expr -> Env ident prim -> Value prim, -- defined in section 3.2
>   valBexpr :: bexpr -> Env ident prim -> CL Bool -- defined in section 3.2
>   }

There are 5 types of nodes:

> data NodeType node ident expr bexpr
>   = NSEntry (Entry node) -- todo: rename to NEntry
>   | NSAssignment (Assignment node ident expr)
>   | NSTest (Test node bexpr)
>   | NSJunction (Junction node)
>   | NSExit (Exit node)

Entry nodes have 1 successor.

> data Entry node = Entry {
>   entrySelf :: node,
>   entrySuccessor :: node }
> 
> entryConnections :: Connections (Entry node) node
> entryConnections = Connections pred succ where
>   pred _ = []
>   succ n = [entrySuccessor n]

Page 239

Assignment nodes assign the value of an expression (expr) to an
identifier (ident). They have one predecessor and one successor.

> data Assignment node ident expr = Assignment {
>   assignmentId :: ident,
>   assignmentExpression :: expr,
>   assignmentPredecessor :: node,
>   assignmentSuccessor :: node }
> 
> assignmentConnections :: Connections (Assignment node ident expr) node
> assignmentConnections = Connections pred succ where
>   pred n = [assignmentPredecessor n]
>   succ n = [assignmentSuccessor n]

Test nodes evaluate a boolean expression. They have one predecessor and
two successors. The successor is chosen based on the value of the boolean.

> data Test node bexpr = Test {
>   testSelf :: node, -- todo: add self function for other types
>   testPredecessor :: node,
>   nSuccT :: node,
>   nSuccF :: node,
>   testExpression :: bexpr }
> 
> testConnections :: Connections (Test node bexpr) node
> testConnections = Connections pred succ where
>   pred n = [testPredecessor n]
>   succ n = [nSuccT n, nSuccF n]

Junction nodes have one successor and more than one predecessor.

> data Junction node = Junction {
>   junctionPredecessors :: [node],
>   junctionSuccessor :: node }
> 
> junctionConnections :: Connections (Junction node) node
> junctionConnections = Connections pred succ where
>   pred = junctionPredecessors
>   succ n = [junctionSuccessor n]

Exit node has one predecessor and no successor.

> data Exit node = Exit {
>   exitPredecessor :: node }
> 
> exitConnections :: Connections (Exit node) node
> exitConnections = Connections pred succ where
>   pred = (:[]) . exitPredecessor
>   succ _ = []

An arc is a pair of nodes connected in the flow chart.

> data Arc node = Arc {
>   origin :: node,
>   end :: node }
>   deriving (Eq)
>
> aSucc :: Connections node node -> node -> [Arc node]
> aSucc conn n = map (Arc n) (nSucc conn n)
>
> aPred :: Connections node node -> node -> [Arc node]
> aPred conn n = map (flip Arc n) (nPred conn n)
>
> aSuccT :: Test node bexpr -> Arc node
> aSuccT n = Arc (testSelf n) (nSuccT n)
>
> aSuccF :: Test node bexpr -> Arc node
> aSuccF n = Arc (testSelf n) (nSuccF n)

Section 3.2, page 239, Semantics of programs

If S is a set, we denote CL S the complete lattice by adding
bottom and top to it.

> data CL a = Top | Bottom | Middle a
>   deriving (Eq, Functor) -- not sure that Eq is appropriate
>
> instance Applicative CL where
>   pure = Middle
>   Top <*> _ = Top
>   _ <*> Top = Top
>   Bottom <*> _ = Bottom
>   _ <*> Bottom = Bottom
>   Middle f <*> Middle x = Middle (f x)
>
> instance Monad CL where
>   return = Middle
>   Top >>= _ = Top
>   Bottom >>= _ = Bottom
>   Middle x >>= f = f x

Values is the complete lattice of booleans and other primitives.

> type WithBool prim = Either Bool prim
> type Value prim = CL (WithBool prim)

Environments map identifiers to values.

> type Env ident prim = CL ident -> Value prim

val and valBexpr were defined in Program.

Every state is a pair of an instruction pointer and an environment.

> data State node ident prim = State {
>   cs :: CL (Arc node),
>   env :: Env ident prim }

cond evaluates boolean expressions.

> cond :: CL Bool -> CL a -> CL a -> CL a
> cond Top _ _ = Top
> cond Bottom _ _ = Bottom
> cond (Middle True) e _ = e
> cond (Middle False) _ e = e

> subst :: (Eq ident) => Env ident prim -> Value prim -> CL ident -> CL ident -> Value prim
> subst e v x = \y -> cond (y =:= x) v (e y)

> (=:=) :: (Eq ident) => CL ident -> CL ident -> CL Bool
> a =:= b = (==) <$> a <*> b

The static transition function defines the behavior of each of
the nodes.

> nState :: (Eq ident) => Program node ident expr bexpr prim -> State node ident prim -> State node ident prim
> nState program s = 
>   let n = fmap end (cs s)
>       e = env s in
>   case fmap (classify program) n of
>      Top -> State Top e
>      Bottom -> State Bottom e
>      Middle t ->
>        case t of
>          NSEntry _ -> error "no state exists before entry node"
>          NSAssignment a ->
>            let ident = assignmentId a
>                expr = assignmentExpression a
>                newEnv Top = Top
>                newEnv Bottom = Bottom
>                newEnv (Middle i) | i == ident = val program expr e
>                                  | otherwise = e (Middle i) in
>            State (fmap (flip Arc (assignmentSuccessor a)) n) newEnv
>          NSTest t -> State (cond (valBexpr program (testExpression t) e) (Middle (aSuccT t)) (Middle (aSuccF t))) e
>          NSJunction j -> State (fmap (flip Arc (junctionSuccessor j)) n) e
>          NSExit _ -> s

The initial environment maps all values to bottom.

> bottomEnv :: Env ident prim
> bottomEnv _ = Bottom

> initialStates :: Program node ident expr bexpr prim -> [State node ident prim]
> initialStates program = map (\entry -> State (Middle (Arc (entrySelf entry) (entrySuccessor entry))) bottomEnv) (entryNodes program)

Page 240

> computationSequence :: (Eq ident) => Program node ident expr bexpr prim -> State node ident prim -> [State node ident prim]
> computationSequence program = iterate (nState program)

For terminating traces, eventually the states returned by computationSequence will all be equivalent, because exit nodes do not change the
state. This could also have been done by having nState return Maybe, terminating computationSequence at the first
Nothing, and getting the last value returned by computationSequence, but for some reason I haven't yet determined, the paper prefers to
define the initial to final state transition function as the least fixed point of nState.

Section 4, page 240, Static semantics of programs

The context for an arc is all possible environments for that arc. Because computationSequence is an infinite
list, the following definition of context will never return environments for any initial states but one.

> type Context ident prim = [Env ident prim]

> type ContextVector node ident prim = CL (Arc node) -> [Env ident prim]

> context :: (Eq ident, Eq node) => Program node ident expr bexpr prim -> ContextVector node ident prim
> context program q = do
>   initialState <- initialStates program
>   State q' e <- computationSequence program initialState
>   guard $ q == q'
>   return e

> envOn :: (Eq node) => CL (Arc node) -> State node ident prim -> [Env ident prim]
> envOn r s = if r == cs s then [env s] else []

> nContext :: (Eq ident, Eq node) => Program node ident expr bexpr prim -> CL (Arc node) -> ContextVector node ident prim -> [Env ident prim]
> nContext program rr cv =
>   case rr of
>     Top -> error "not implemented: nContext top"
>     Bottom -> error "not implemented: nContext bottom"
>     Middle r ->
>       case classify program $ origin r of
>         NSEntry _ -> [bottomEnv]
>         _ -> do
>           q <- aPred (connections program) (origin r)
>           e <- cv (Middle q)
>           envOn (Middle r) (nState program (State (Middle q) e))

Top of page 240, second column

> fCont :: (Eq ident, Eq node) => Program node ident expr bexpr prim -> ContextVector node ident prim -> ContextVector node ident prim
> fCont program cv = \r -> nContext program r cv

ContextVector is a complete lattice with union `mappend`.

> instance Monoid (ContextVector node ident prim) where
>   mempty = const []
>   cv1 `mappend` cv2 = \r -> cv1 r `mappend` cv2 r

Then lots of stuff that I don't quite understand.

Section 5 on page 240, Abstract interpretation of programs

> data AbstractInterpretation node aCont = AbstractInterpretation {
>   joinContext :: aCont -> aCont -> aCont,
>   lte :: aCont -> aCont -> Bool, -- x `lte` y <=> x `joinContext` y == y
>   top :: aCont,
>   bottom :: aCont,
>   interpret :: CL (Arc node) -> Tilda node aCont -> aCont {- defined on page 241 -} }

Page 241

> type Tilda node a = CL (Arc node) -> a

> tildaJoinContext :: AbstractInterpretation node aCont -> Tilda node aCont -> Tilda node aCont -> Tilda node aCont
> tildaJoinContext ai cv' cv'' = \r -> joinContext ai (cv' r) (cv'' r)

> tildaLTE :: AbstractInterpretation node aCont -> Tilda node aCont -> Tilda node aCont -> Bool
> tildaLTE ai cv' cv'' = all (\r -> lte ai (cv' r) (cv'' r)) (allArcs ai) where
>   allArcs _ = undefined -- todo; probably need to pass in a program

tildaLTE ai cv' cv'' implies that lte ai (interpret ai a cv') (interpret ai a cv'') for all a in arcs.

Section 5.3.1, page 241, static semantics of programs

> staticSemantics :: (Eq ident, Eq node) => Program node ident expr bexpr prim -> AbstractInterpretation node (Context ident prim)
> staticSemantics program = AbstractInterpretation mappend subset allEnvs [] (nContext program) where
>   subset = undefined -- todo
>   allEnvs = undefined -- todo; we probably need to extend type to include a top value

Section 5.3.2 Data Flow Analysis

> type BVect node expr = Arc node -> expr -> Bool

> avail ::
>   Program node ident expr bexpr prim ->
>   (node -> expr -> Bool) ->
>   (node -> expr -> Bool) ->
>   Arc node ->
>   BVect node expr ->
>   expr -> Bool
> avail program generated transparent r bv =
>   let n = origin r in
>   case classify program $ n of
>     NSEntry _ -> \_ -> False
>     _ -> \e -> generated n e || flip all (aPred (connections program) n) (\p -> bv p e && transparent n e)

^ not really sure about this one. It seems like there should be some transitive calculation going on here
  (the paper uses the phrase "for all predecessors"), yet the definition does no such thing. Also,
  the paper actually defines `type BVector node expr = expr -> Bool`, but I had to add the extra argument
  `Arc node` in order to get it to type check

