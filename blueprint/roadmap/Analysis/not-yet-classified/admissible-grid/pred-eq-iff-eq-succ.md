# Pred eq iff eq succ

Equality after a backward step is equivalent to equality before its inverse forward step.

```lean
theorem pred_eq_iff_eq_succ (v w : GridIndex) (i : Fin 2) :
    v.pred i = w ↔ v = w.succ i
```
