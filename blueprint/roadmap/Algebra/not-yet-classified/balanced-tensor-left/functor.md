# Functor

Let `k` be a commutative ring, `R` a `k`-algebra, and `S` a ring. Let `Q` be
an additive commutative group with `k`, right `R`, and left `S` module actions.
Assume the `S` action commutes with both the `k` and right `R` actions. The functor sends
a left `R`-module `N` to `TensorProduct.Balanced k R Q N` as a left
`S`-module, and `g : N ⟶ N′` to the map sending `[q, n]` to `[q, g n]`.
The `S` action is on the first factor and the `k` action on `N`
is obtained by restriction of scalars.
