# Circle Mean

For positive radius, the real angle integral from zero to `2π` of the analytic circle values is
`2π` times the center value.

```lean
theorem circle_integral_center (f : ℂ → ℂ) (a : ℂ) (r : ℝ) (hr : 0 < r)
    (hf : AnalyticOn ℂ f (closedBall a r)) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, f (circleMap a r θ)) =
      (2 * Real.pi) • f a
```
