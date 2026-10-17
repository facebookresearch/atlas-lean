---
article_id: af_b762d7cb743b516b73b90e71
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.generalizedCatalan_prime_dvd_iff_not_geometric_sum
---

# Generalized Catalan Prime Divisibility

A prime `p` divides the generalized Catalan number `C (p * n) n / ((p - 1) * n + 1)`
if and only if `n` is not a geometric-sum index `(p ^ k - 1) / (p - 1)`.

The source theorem's "in particular" Mersenne-index clause is already recorded
as `catalan_odd_iff`; this declaration keeps only the new general-`p` result.
Proves `Wanted` entry `generalizedCatalan_prime_dvd_iff_not_geometric_sum`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Fuss Catalan Divisibility](../../../Combinatorics/MathlibExt/part-01/enumerative/part-03/fuss-catalan-dvd-choose.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.GeneralizedCatalanPrimeDivisibility](../../../../sources/v2/MathlibExt.md)
- B. Sury, "Generalized Catalan Numbers: Linear Recursion and Divisibility," Journal of Integer Sequences 12 (2009), Article 09.7.5, Theorem (label divis), lines 154–158, https://cs.uwaterloo.ca/journals/JIS/VOL12/Sury/sury31.tex
