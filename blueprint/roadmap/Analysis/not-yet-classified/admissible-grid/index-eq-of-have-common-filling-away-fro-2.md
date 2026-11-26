# Index eq of have Common Filling Away From of is Admissible For

For admissible fillings, the trace hypotheses in the discrete-Stokes
bridge follow automatically outside `G \ K`.

```lean
theorem index_eq_of_haveCommonFillingAwayFrom_of_isAdmissibleFor
    {D E : GridFilling} {K G : Set ℂ} (hD : D.IsAdmissibleFor K G)
    (hE : E.IsAdmissibleFor K G) (hDE : D.HaveCommonFillingAwayFrom E K G)
    {z : ℂ} (hz : z ∉ G \ K) : D.toCycle.index z = E.toCycle.index z
```
