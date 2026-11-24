# Functor

Let `k` be a commutative ring, `R` a `k`-algebra with possibly noncommutative
`R`, and `M` an additive commutative group with a `k`-module action and a
right `R`-module action (a left `Rᵐᵒᵖ`-module action). The functor from
left `R`-modules to `k`-modules sends `N` to `TensorProduct.Balanced k R M N`
and a morphism `g : N ⟶ N′` to the map induced by `(m, n) ↦ (m, g n)`.
The `k` action on `N` is obtained by restriction of scalars.
