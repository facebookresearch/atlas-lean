# Succ eq iff eq pred

Equality after a forward step is equivalent to equality before its inverse backward step.

```lean
theorem succ_eq_iff_eq_pred (v w : GridIndex) (i : Fin 2) :
    v.succ i = w ↔ v = w.pred i
```
