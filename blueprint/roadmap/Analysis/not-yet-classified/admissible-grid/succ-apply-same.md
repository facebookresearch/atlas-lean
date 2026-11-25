# Succ apply same

A forward step increases its chosen integer coordinate by one.

```lean
theorem succ_apply_same (v : GridIndex) (i : Fin 2) : v.succ i i = v i + 1
```
