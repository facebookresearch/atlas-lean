# Permutations moving only fresh atoms fix the element

A permutation that fixes every atom outside a finite set `F` of fresh
atoms fixes `x`, by induction on `F`. If `π a = a` we apply the induction
hypothesis to `π`; otherwise we factor `π = swap a b * π'` with `b = π a`,
where `π'` fixes `a` and has support inside `F \ {a}`, and `swap a b` fixes
`x` since `a` and `b` are fresh.
