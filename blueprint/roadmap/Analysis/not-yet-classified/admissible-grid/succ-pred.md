# Succ pred

A forward step followed by the matching backward step returns the original index.

```lean
theorem succ_pred (v : GridIndex) (i : Fin 2) : (v.succ i).pred i = v
```
