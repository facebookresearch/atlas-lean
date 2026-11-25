# Anchor independence of Burgers evolution

For continuous bounded real initial velocity and positive viscosity, the Cole–Hopf Burgers field has the same value for every spatial normalization anchor, at every nonnegative time and every spatial point. The comparison includes time zero.

## Exact statement

```lean
theorem burgersSolution_anchor_independent {u₀ : ℝ → ℝ} (hu : Continuous u₀)
    (hb : ∃ M, ∀ x, |u₀ x| ≤ M) {ν : ℝ} (hν : 0 < ν) (a b t x : ℝ) (ht : 0 ≤ t) :
    burgersSolution ν u₀ a t x = burgersSolution ν u₀ b t x
```

## Proof

Identify both fields by bounded classical uniqueness and their common initial data.
