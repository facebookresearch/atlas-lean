---
article_id: af_4722b13fee03f1b646de801a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.pell_binomial_transform
---

# Pell Binomial Transform

The binomial transform of the Pell numbers equals the stated Kronecker-symbol
sum: `∑_i C(n,i) P_i = ∑_k (k/8) C(2n,n+k)`.

The Kronecker symbol `(k/8)` is spelled out via `k mod 8`: even `k` gives `0`,
`k ≡ ±1` gives `1`, `k ≡ ±3` gives `-1`. The Pell sequence is pinned by its
initial values and recurrence; both sides give `0, 1, 4, 14, 48, 164, ...`
(A007070) at `n = 0..5`, verified through `n = 7`.
Proves `Wanted` entry `pell_binomial_transform`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Recurrences.PellBinomialTransform](../../../../../../sources/v2/MathlibExt.md)
- Greg Dresden and Yike Li, "Periodic Weighted Sums of Binomial Coefficients," Journal of Integer Sequences 26 (2023), Article 23.8.7, Corollary (equation e.12), lines 369–379, https://cs.uwaterloo.ca/journals/JIS/VOL26/Dresden/dresden26.tex
