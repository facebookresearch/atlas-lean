# Burgers velocity as a Gaussian first moment

For bounded continuous initial velocity, positive viscosity and strictly positive time, the Cole–Hopf velocity equals x/t minus a normalized first Gaussian moment of its initial heat profile, as displayed in the complete formula below. The anchor is arbitrary. No zero-time formula is claimed.

## Exact statement

```lean
theorem burgersSolution_eq_gaussianMoment {u : ℝ → ℝ} (hu : Continuous u)
    (hb : ∃ M, ∀ x, |u x| ≤ M) {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (a x : ℝ) :
    burgersSolution ν u a t x = x / t -
      gaussianMoment (initialHeatProfile ν u a) 1 (1 / (4 * (ν * t)), x / (2 * (ν * t))) /
        (t * gaussianMoment (initialHeatProfile ν u a) 0
          (1 / (4 * (ν * t)), x / (2 * (ν * t))))
```

## Proof

Use exponential growth to justify Gaussian moments, then rewrite the heat profile logarithmic derivative.
