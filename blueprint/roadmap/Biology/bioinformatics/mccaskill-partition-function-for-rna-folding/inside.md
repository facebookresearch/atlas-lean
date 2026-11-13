# Inside recursion

**Inside recursion** over a commutative semiring `R`: `inside pair m s w i len` is the
weighted sum over the secondary structures supported in the interval `[i, i + len)` (proved in
`inside_eq_sum`). Base `i` is either unpaired, or paired with `i + 1 + k` for some `k ≥ m`
with `CanPair pair s i (i + 1 + k)`, which contributes `w i (i + 1 + k)` times the inside
values of the enclosed interval `[i + 1, i + 1 + k)` and of the outer interval
`[i + k + 2, i + len + 1)`.
