---
article_id: af_efb719263c71836f7deb6231
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.chu_vandermonde_terminating_specialization
---

# Chu Vandermonde Terminating Specialization

Chu–Vandermonde summation for a terminating Gauss hypergeometric series:
`∑ k ∈ Finset.range (n + 1), (n.choose k) * ((n + k).choose k) * (-1)^k / (k + 1) = 0`
for `1 ≤ n`. The source identifies the sum as
`₂F₁(n+1, -n; 2; 1) = (1-n)_n / (2)_n = 0`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.ChuVandermondeTerminatingSpecialization](../../../../../../sources/v2/MathlibExt.md)
- Carsten Elsner, "On Prime-Detecting Sequences From Apéry's Recurrence Formulae for ζ(3) and ζ(2)", Journal of Integer Sequences 11 (2008), Article 08.5.1, lines 606–608, <https://cs.uwaterloo.ca/journals/JIS/VOL11/Elsner/elsner7.tex>. Proves `Wanted` entry `chu_vandermonde_terminating_specialization`.
