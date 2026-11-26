# Cell Multiplicity eq of have Common Filling Away From

Under the common-filling condition, the multiplicities agree outside `G \ K`.

```lean
theorem cellMultiplicity_eq_of_haveCommonFillingAwayFrom
    {D E : GridFilling} {K G : Set ℂ} (hDE : D.HaveCommonFillingAwayFrom E K G)
    {z : ℂ} (hz : z ∉ G \ K) : D.cellMultiplicity z = E.cellMultiplicity z
```
