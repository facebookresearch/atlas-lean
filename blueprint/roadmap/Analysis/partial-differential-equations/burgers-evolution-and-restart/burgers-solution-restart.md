# Restart of the explicit Burgers evolution

For positive viscosity and bounded continuous initial velocity, evolving for a nonnegative duration and then evolving the resulting spatial field for another nonnegative duration equals evolution for the sum. The two constructions may use different normalization anchors; both zero-duration cases are included.

## Exact statement

```lean
theorem burgersSolution_restart {u₀ : ℝ → ℝ} (hu : Continuous u₀)
    (hb : ∃ M, ∀ x, |u₀ x| ≤ M) {ν : ℝ} (hν : 0 < ν)
    (a b s t x : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    burgersSolution ν (burgersSolution ν u₀ a s) b t x =
      burgersSolution ν u₀ a (s + t) x
```

## Proof

Apply the classical restart theorem to the explicit solution, using bound preservation and its initial-time continuity.
