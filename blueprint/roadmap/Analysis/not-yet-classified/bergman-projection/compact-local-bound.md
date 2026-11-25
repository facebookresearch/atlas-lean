# Compact local bound

Every compact subset of an open planar domain has a positive uniform bound on analytic
representative differences in terms of L2 class differences.

```lean
theorem compact_local_bound (G : Set ℂ) (hG : IsOpen G) (K : Set ℂ)
    (hKG : K ⊆ G) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f h : Lp ℂ 2 (volume.restrict G)) (g k : ℂ → ℂ),
      AnalyticOn ℂ g G → AnalyticOn ℂ k G →
      (∀ᵐ z ∂volume.restrict G, f z = g z) →
      (∀ᵐ z ∂volume.restrict G, h z = k z) →
      ∀ z ∈ K, ‖g z - k z‖ ≤ C * ‖f - h‖
```
