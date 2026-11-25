# Pow Tuple Equiv

Head-first power equivalence, via the generalized reader at `PUnit`.

`(monadPow (tensorMonad G) n).obj PUnit` is the left-nested product
`G × (G × ... × PUnit)`; `t 0` is the outermost factor. Defining it through
`powTupleGen` keeps a single recursion principle: every tuple interaction
(zero/last/middle faces, degeneracies) is proved once for general `X` and
specialized here by dropping the terminal `PUnit` factor.
