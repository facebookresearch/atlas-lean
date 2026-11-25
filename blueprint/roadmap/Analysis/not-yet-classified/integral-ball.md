# Translated Area Mean

The planar volume integral over the open disk centered at `a` is `πr²` times the analytic value
at `a`.

```lean
theorem integral_ball (f : ℂ → ℂ) (a : ℂ) (r : ℝ) (hr : 0 < r)
    (hf : AnalyticOn ℂ f (closedBall a r)) :
    (∫ z in ball a r, f z) = (Real.pi * r ^ 2) • f a
```
