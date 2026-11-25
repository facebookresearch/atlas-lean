# Measurable Set angular Sublevel Set

For a nonpositive subharmonic function on the unit disk and `0<r<1`,
the full-period strict angular sublevel set is measurable.

```lean
theorem measurableSet_angularSublevelSet
    {u : ℂ → EReal} {r K : ℝ}
    (hu : IsNonpositiveSubharmonicOn u (Metric.ball 0 1))
    (hr0 : 0 < r) (hr1 : r < 1) :
    MeasurableSet (angularSublevelSet u r K)
```
