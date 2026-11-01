---
article_id: af_3a443d2c504bd5805254d106
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.staver_reciprocal_binomial_sum
---

# Staver Reciprocal Binomial Sum

Staver reciprocal binomial sum (Sprugnoli, JIS VOL14).
Stable record `jis_grounded_c6a8cb740924fc3bd0e3537c`, concept
`jis_dep_885d07be0a43a0e708255663`.

Both sides satisfy the same recurrence `F (n + 1) = 1 + ((n + 2) / (2 * (n + 1)))
* F n`, so the identity follows by induction on `n`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.StaverReciprocalBinomialSum](../../../../sources/v2/MathlibExt.md)
- <https://cs.uwaterloo.ca/journals/JIS/VOL14/Sprugnoli/sprugnoli4.tex>. Source SHA-256: `ae40930a75b3cf8f936a17aa41ee135b01fca41ec402a441f0cf3b0ffdc50111`. Definition lines 115-125, span SHA `32e139d381bbe240e14ebcd608096af53038b9b0943d71ed20ce5a97e2cb32ab`. Formula lines 231-236, span SHA `b302dbad07d413045e3022c045503c521bbcfeeec710cc24ff4950d9825da66d`. The left side expands `S_n^(0)`, the sum of reciprocal binomial coefficients. All arithmetic is rational (`Rat` division and inverses); the statement holds for all `n : Nat`, so the edge case `n = 0` is included.
