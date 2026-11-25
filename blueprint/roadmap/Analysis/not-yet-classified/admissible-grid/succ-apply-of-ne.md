# Succ apply of ne

A forward step leaves every other integer coordinate unchanged.

```lean
theorem succ_apply_of_ne (v : GridIndex) {i j : Fin 2} (h : j ≠ i) :
    v.succ i j = v j
```
