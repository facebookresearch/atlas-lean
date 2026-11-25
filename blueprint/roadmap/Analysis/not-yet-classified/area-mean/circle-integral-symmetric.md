# Circle integral symmetric

The analytic circle mean over the open angle interval `(-π,π)` is `2π` times the value at zero.

```lean
theorem circle_integral_symmetric (f : ℂ → ℂ) (r : ℝ) (hr : 0 < r)
    (hf : AnalyticOn ℂ f (closedBall 0 r)) :
    (∫ θ in Ioo (-Real.pi) Real.pi, f (circleMap 0 r θ)) =
      (2 * Real.pi) • f 0
```
