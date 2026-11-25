# Pred apply of ne

A backward step leaves every other integer coordinate unchanged.

```lean
theorem pred_apply_of_ne (v : GridIndex) {i j : Fin 2} (h : j ≠ i) :
    v.pred i j = v j
```
