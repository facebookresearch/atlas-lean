# Pred succ

A backward step followed by the matching forward step returns the original index.

```lean
theorem pred_succ (v : GridIndex) (i : Fin 2) : (v.pred i).succ i = v
```
