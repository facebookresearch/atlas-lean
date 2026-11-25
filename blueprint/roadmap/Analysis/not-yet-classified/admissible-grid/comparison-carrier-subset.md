# Comparison Carrier subset

If both traces and their common-filling support lie in `G \ K`, so does the comparison carrier.

```lean
theorem comparisonCarrier_subset {D E : GridFilling} {K G : Set ℂ}
    (hD : D.reducedTrace ⊆ G \ K) (hE : E.reducedTrace ⊆ G \ K)
    (hDE : D.HaveCommonFillingAwayFrom E K G) :
    D.comparisonCarrier E ⊆ G \ K
```
