# Equiv Of Equivalence

`K₀` is invariant under exact equivalence: an equivalence of categories whose
functor and inverse are additive and exact induces an additive equivalence on `K₀`.

The construction uses `K0.map` in both directions; the inverse identities follow
from `K0.map_comp`, `K0.map_eq_of_iso`, `K0.map_id` and the unit/counit
natural isomorphisms of the equivalence.
