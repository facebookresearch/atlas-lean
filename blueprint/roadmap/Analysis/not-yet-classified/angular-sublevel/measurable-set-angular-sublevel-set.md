# Measurable Set angular Sublevel Set

**Measurability of strict angular sublevel sets.** Let `u : ℂ → EReal` be upper
semicontinuous on the open unit disk. For real `r,K` with `|r| < 1`, the angles
`θ ∈ (0,2π]` satisfying `u(circleMap 0 r θ) < -K` form a measurable set.
Zero and negative radii are included, and the threshold `K` is arbitrary.

```lean
theorem measurableSet_angularSublevelSet
    {u : ℂ → EReal} {r K : ℝ}
    (hu : UpperSemicontinuousOn u (Metric.ball 0 1))
    (hr : |r| < 1) :
    MeasurableSet (angularSublevelSet u r K)
```
