# Exists submodule

There exists a complex L2 submodule with exactly the analytic-representative membership
characterization.

```lean
theorem exists_submodule (G : Set ℂ) (μ : Measure ℂ) :
    ∃ B : Submodule ℂ (Lp ℂ 2 μ),
      ∀ f, f ∈ B ↔ ∃ g : ℂ → ℂ, AnalyticOn ℂ g G ∧ ∀ᵐ z ∂μ, f z = g z
```
