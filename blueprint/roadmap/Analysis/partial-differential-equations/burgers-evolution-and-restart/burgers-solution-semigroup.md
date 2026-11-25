# Semigroup law for Burgers evolution

For positive viscosity and bounded continuous initial velocity, the Cole–Hopf evolution at two successive nonnegative times equals evolution for their sum, as equality of spatial functions. A single arbitrary normalization anchor is fixed.

## Exact statement

```lean
theorem burgersSolution_semigroup {u₀ : ℝ → ℝ} (hu : Continuous u₀)
    (hb : ∃ M, ∀ x, |u₀ x| ≤ M) {ν : ℝ} (hν : 0 < ν)
    (a s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    burgersSolution ν (burgersSolution ν u₀ a s) a t = burgersSolution ν u₀ a (s + t)
```

## Proof

Apply the pointwise restart identity at each spatial point.
