# Polynomial adjunction correspondence reads the variable images

Let `k` be a commutative ring in universe `u` and
`T=max(u,v)`. The polynomial free functor sends types in `T` to
commutative `k`-algebras with carriers in `T`. Let `A` be a commutative `k`-algebra with carrier in `T`. For `X : Type T` and a `k`-algebra map
`f : MvPolynomial X k → A`, the associated function on variables
has value `x ↦ f(X(x))`.
