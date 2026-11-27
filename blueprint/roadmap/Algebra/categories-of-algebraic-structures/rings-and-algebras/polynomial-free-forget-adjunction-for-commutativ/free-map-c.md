# Polynomial renaming fixes base coefficients

Let `k` be a commutative ring in universe `u` and
`T=max(u,v)`. The polynomial free functor sends types in `T` to
commutative `k`-algebras with carriers in `T`. Let `X,Y : Type T` and `f : X → Y`. For each `c : k`, the induced map
`MvPolynomial X k → MvPolynomial Y k` sends the source constant
polynomial `C(c)` to the target constant polynomial `C(c)`.
