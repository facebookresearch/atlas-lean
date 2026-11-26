# Pred apply same

A backward step decreases its chosen integer coordinate by one.

```lean
theorem pred_apply_same (v : GridIndex) (i : Fin 2) : v.pred i i = v i - 1
```
