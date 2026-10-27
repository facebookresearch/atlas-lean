---
article_id: af_69bfebf7b5eb841dab58b4c2
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.double_binomial_sum_eq_single_binomial_sum
---

# Double Binomial Sum Reduction

Double binomial absolute-power sum reduces to a single binomial sum:
`T_β(m,n) = S_β(m+n)`.

The centered indices `k, ℓ` are reindexed to `i = m + k`, `j = n + ℓ`
(resp. `k = m + n + d`), so `|k - ℓ|` becomes `|(i - m) - (j - n)|`;
the `Finset.range` bounds cover exactly the nonzero binomial support.
This is the reduction theorem, distinct from the same paper's closed form
for `W_1(n)` (label thm:S12).
Proves `Wanted` entry `double_binomial_sum_eq_single_binomial_sum`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.DoubleBinomialSumReduction](../../../../../../sources/v2/MathlibExt.md)
- Richard P. Brent, Hideyuki Ohtsuka, Judy-anne H. Osborn, and Helmut Prodinger, "Some Binomial Sums Involving Absolute Values," Journal of Integer Sequences 19 (2016), Article 16.3.7, Theorem (label thm:reduce2to1), lines 278–283 (with `S_β` defined at lines 245–247 and `T_β` at 271–274), https://cs.uwaterloo.ca/journals/JIS/VOL19/Brent/brent9.tex
