# Ground Iso

Let `k` be a commutative ring, `R` a `k`-algebra, and `S` a ring. Let `Q` be
an additive commutative group with `k`, right `R`, and left `S` module actions.
Assume the `S` action commutes with both the `k` and right `R` actions. Assume also that
`S` is a `k`-algebra and `IsScalarTower k S Q` holds.
Then `functor k R S Q ⋙ ModuleCat.restrictScalars (algebraMap k S)`
is naturally isomorphic to `ModuleCat.BalancedTensor.functor k R Q`.
Each component takes a balanced tensor class to that same class.
