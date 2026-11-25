# Order preservation with independent anchors

For positive viscosity and bounded continuous initial velocities u ≤ v pointwise, the corresponding Cole–Hopf fields remain ordered at every nonnegative time, even when constructed with independent normalization anchors.

## Exact statement

```lean
theorem burgersSolution_mono_of_anchors {u v : ℝ → ℝ}
    (hu : Continuous u) (hv : Continuous v)
    (hbu : ∃ M, ∀ x, |u x| ≤ M) (hbv : ∃ M, ∀ x, |v x| ≤ M)
    {ν : ℝ} (hν : 0 < ν) (h : ∀ x, u x ≤ v x) (a b : ℝ)
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    burgersSolution ν u a t x ≤ burgersSolution ν v b t x
```

## Proof

Combine order preservation for a common anchor with anchor independence.
