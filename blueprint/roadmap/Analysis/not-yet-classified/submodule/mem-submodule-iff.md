# Mem submodule iff

Membership is precisely existence of an analytic-on-`G` representative with the displayed
almost-everywhere equality for `μ`.

```lean
theorem mem_submodule_iff (G : Set ℂ) (μ : Measure ℂ) (f : Lp ℂ 2 μ) :
    f ∈ submodule G μ ↔ ∃ g : ℂ → ℂ, AnalyticOn ℂ g G ∧ ∀ᵐ z ∂μ, f z = g z
```
