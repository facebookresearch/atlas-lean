---
article_id: af_69fc118e7f03e7e40c9d031e
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.brent_osborn_binomial_absolute_moment
---

# Brent Osborn Binomial Absolute Moment

The Brent–Osborn binomial absolute moment identity: the centered double sum
`W₁(n) = Σ_{k,ℓ} C(2n,n+k) C(2n,n+ℓ) |k²−ℓ²|` equals `2n² C(2n,n)²`.
The sum is reindexed to `k, ℓ ∈ Fin (2 * n + 1)` with `k.1 - n` for the
source's centered index; this has the same support since
`C(2n, n+k) = 0` for `|k| > n`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.BrentOsbornBinomialAbsoluteMoment](../../../../../../sources/v2/MathlibExt.md)
- Richard P. Brent, Hideyuki Ohtsuka, Judy-anne H. Osborn, and Helmut Prodinger, "Some Binomial Sums Involving Absolute Values," Journal of Integer Sequences 19 (2016), Article 16.3.7, Theorem [Brent and Osborn] (label thm:S12), lines 377–383 (with the `W_β` definition at lines 345–349), https://cs.uwaterloo.ca/journals/JIS/VOL19/Brent/brent9.tex
