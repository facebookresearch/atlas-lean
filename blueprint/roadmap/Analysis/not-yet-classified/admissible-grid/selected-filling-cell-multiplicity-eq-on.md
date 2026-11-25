# Selected Filling cell Multiplicity eq one of mem

Every point of the compact set has multiplicity one in its selected filling.

```lean
theorem selectedFilling_cellMultiplicity_eq_one_of_mem
    (K : Set ℂ) {r t : ℝ} (ht : 0 < t) (hK : IsCompact K)
    {z : ℂ} (hz : z ∈ K) :
    (selectedFilling K r t ht hK).cellMultiplicity z = 1
```
