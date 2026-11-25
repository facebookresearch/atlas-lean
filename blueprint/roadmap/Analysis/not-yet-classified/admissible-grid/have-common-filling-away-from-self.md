# Have Common Filling Away From self

A filling has the common-filling-away-from condition with itself for arbitrary sets.

```lean
theorem haveCommonFillingAwayFrom_self (D : GridFilling) (K G : Set ℂ) :
    D.HaveCommonFillingAwayFrom D K G
```
