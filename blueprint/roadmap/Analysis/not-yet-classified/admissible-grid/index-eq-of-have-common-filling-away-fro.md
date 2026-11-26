# Index eq of have Common Filling Away From

Discrete-Stokes bridge supplied by the subdivision-invariant common
filling condition: the two analytic indices agree away from the comparison
region, whenever the point is off both reduced boundaries.

```lean
theorem index_eq_of_haveCommonFillingAwayFrom
    {D E : GridFilling} {K G : Set ℂ} (hDE : D.HaveCommonFillingAwayFrom E K G)
    {z : ℂ} (hz : z ∉ G \ K) (hzD : z ∉ D.reducedTrace)
    (hzE : z ∉ E.reducedTrace) : D.toCycle.index z = E.toCycle.index z
```
