# Pow Tuple Gen succ fst

Successor tuple: the generalized reader exposes `Fin.snoc`.

Stable API for `powTupleGen`: the `n + 1` tuple is the `n` tuple at
`T.obj X` with the head factor snoc'd on. A later one-file repair in
`ClassifyingNerveNaturality.lean` consumes this instead of mirroring the
recursion.
