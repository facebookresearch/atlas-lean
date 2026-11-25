# Overlay Box subset i Union iff mem

For aligned partitions, an overlay box lies wholly in the first union exactly when a given
point of that box lies there.

```lean
theorem overlayBox_subset_iUnion_iff_mem
    {B : BoxIntegral.Box (Fin 2)} (π ρ : BoxIntegral.Prepartition B)
    (halign : π ⊓ ρ = ρ.filter fun J ↦ (J : Set (Fin 2 → ℝ)) ⊆ π.iUnion)
    {I : BoxIntegral.Box (Fin 2)} (hI : I ∈ ρ) {x : Fin 2 → ℝ}
    (hx : x ∈ I) :
    (I : Set (Fin 2 → ℝ)) ⊆ π.iUnion ↔ x ∈ π.iUnion
```
