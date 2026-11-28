# Skew Cost

`cost` for skew heaps. Same totalisation remark as for `skewExec`:
Isabelle's equations cover only arity-matching lists; the fallback
is `0`, and it is never used on a `wf` history. `Del_min` cost is
written as `T_delMin t + 1`, which equals Isabelle's case split
(`Leaf ↦ 1`, `Node ↦ T_merge + 1`).
