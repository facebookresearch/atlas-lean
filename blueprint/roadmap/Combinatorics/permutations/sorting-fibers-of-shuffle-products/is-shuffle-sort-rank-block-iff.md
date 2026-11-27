# The rank shuffle condition is two sorting conditions

Let `p,q,m : ℕ`, `s : Shuffle p q`, `α ∈ S_p`, `β ∈ S_q`, and `f : Fin(p+q) → Fin m`. Split
`f` along the value blocks of `s` into `(g,h)`. Then `(Tuple.sort f)⁻¹ * (s.perm *
blockPermutation p q α β)` is a `(p,q)`-shuffle if and only if `Tuple.sort g = α` and
`Tuple.sort h = β`.
