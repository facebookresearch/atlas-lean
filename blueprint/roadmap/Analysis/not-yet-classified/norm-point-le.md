# Evaluation Bound

At the center of a positive-radius closed disk contained in `G`, an analytic representative is
bounded by the stated square-root-area constant times its L2 class norm.

```lean
theorem norm_point_le (G : Set ℂ) (g : ℂ → ℂ) (hg : AnalyticOn ℂ g G)
    (f : Lp ℂ 2 (volume.restrict G))
    (hfg : ∀ᵐ z ∂volume.restrict G, f z = g z)
    (a : ℂ) (r : ℝ) (hr : 0 < r) (hDisk : closedBall a r ⊆ G) :
    ‖g a‖ ≤ (Real.pi * r ^ 2) ^ (1 / 2 : ℝ) / (Real.pi * r ^ 2) * ‖f‖
```
