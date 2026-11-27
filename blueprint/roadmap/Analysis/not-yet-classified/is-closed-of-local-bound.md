# Closedness

A positive uniform analytic difference estimate on every compact subset of an open domain makes
its restricted-volume analytic L2 submodule closed.

```lean
theorem isClosed_of_local_bound (G : Set ℂ) (hG : IsOpen G)
    (hBound : ∀ K : Set ℂ, K ⊆ G → IsCompact K →
      ∃ C : ℝ, 0 < C ∧ ∀ (f h : Lp ℂ 2 (volume.restrict G)) (g k : ℂ → ℂ),
        AnalyticOn ℂ g G → AnalyticOn ℂ k G →
        (∀ᵐ z ∂volume.restrict G, f z = g z) →
        (∀ᵐ z ∂volume.restrict G, h z = k z) →
        ∀ z ∈ K, ‖g z - k z‖ ≤ C * ‖f - h‖) :
    IsClosed (submodule G (volume.restrict G) : Set (Lp ℂ 2 (volume.restrict G)))
```
