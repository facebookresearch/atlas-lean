# Have Common Filling Away From comm

The common-filling-away-from condition is symmetric in the two fillings.

```lean
theorem haveCommonFillingAwayFrom_comm (D E : GridFilling) (K G : Set ℂ) :
    D.HaveCommonFillingAwayFrom E K G ↔ E.HaveCommonFillingAwayFrom D K G
```
