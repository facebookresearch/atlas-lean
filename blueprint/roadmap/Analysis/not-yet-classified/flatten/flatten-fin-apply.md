# Flatten Fin apply

Let `A` be a coefficient type. For natural numbers `m`, `n`, `p` and `q`, `M : CStarMatrix (Fin m)
(Fin n) (CStarMatrix (Fin p) (Fin q) A)`, `x : Fin (m * p)` and `y : Fin (n * q)`. Exact entry
action of finite nested-matrix flattening. Flat indices are decomposed using the inverse of
`finProdFinEquiv`.
