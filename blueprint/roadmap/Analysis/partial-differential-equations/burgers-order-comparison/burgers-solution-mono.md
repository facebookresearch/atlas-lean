# Order preservation of Burgers evolution

For positive viscosity, two bounded continuous initial velocities ordered pointwise produce ordered Cole–Hopf velocities at every nonnegative time and every spatial point. A common arbitrary normalization anchor is used. The statement includes time zero and does not require initial derivatives.

## Exact statement

```lean
theorem burgersSolution_mono {u v : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hbu : ∃ M, ∀ x, |u x| ≤ M) (hbv : ∃ M, ∀ x, |v x| ≤ M)
    {ν : ℝ} (hν : 0 < ν) (h : ∀ x, u x ≤ v x) (a : ℝ)
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    burgersSolution ν u a t x ≤ burgersSolution ν v a t x
```

## Proof

Compare Gaussian first moments using monotonicity of the initial profile ratio and the cross-product moment inequality.
