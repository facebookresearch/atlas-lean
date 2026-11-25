# Have Common Filling Away From of is Admissible For

Any two admissible grid fillings have subdivision-invariant comparison
support inside the collar domain.

```lean
theorem haveCommonFillingAwayFrom_of_isAdmissibleFor
    {D E : GridFilling} {K G : Set ℂ}
    (hD : D.IsAdmissibleFor K G) (hE : E.IsAdmissibleFor K G) :
    D.HaveCommonFillingAwayFrom E K G
```
