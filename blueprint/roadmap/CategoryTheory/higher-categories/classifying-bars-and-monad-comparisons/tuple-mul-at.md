# Tuple Mul At

Multiply-adjacent tuple: collapse entries `m` and `m + 1` of a head-first
tuple via pinned Mathlib `Fin.contractNth` at `m.castSucc` with `(· * ·)`.
Below keeps the entry (`Fin.contractNth_apply_of_lt`), at multiplies the pair
(`Fin.contractNth_apply_of_eq`), above shifts down
(`Fin.contractNth_apply_of_gt`).
