# Integral ball zero

The planar volume integral over the open zero-centered disk is its area `πr²` times the
analytic center value.

```lean
theorem integral_ball_zero (f : ℂ → ℂ) (r : ℝ) (hr : 0 < r)
    (hf : AnalyticOn ℂ f (closedBall 0 r)) :
    (∫ z in ball (0 : ℂ) r, f z) = (Real.pi * r ^ 2) • f 0
```
