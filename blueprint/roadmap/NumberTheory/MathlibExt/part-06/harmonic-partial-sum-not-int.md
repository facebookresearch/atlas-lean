---
article_id: af_4a2454c7b0e39a68e605fdd4
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.harmonic_partial_sum_not_int
---

# Harmonic Partial Sum

For `n ≥ 2`, the sum `∑_{ν=2}^n H_ν` of classical harmonic numbers is not
an integer. The source proves this via its identity
`∑_{ν=2}^n H_ν = (n+1)(H_n - 1)` (equation (1.2)), reducing to the
non-integrality of `(n+1) * H_n`, in the spirit of Theisinger's theorem
that `H_n` itself is never integral for `n > 1`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.HarmonicPartialSum](../../../../sources/v2/MathlibExt.md)
- Horst Alzer and Man Kam Kwong, "Ramanujan and a Combinatorial Identity Involving Harmonic Numbers," Journal of Integer Sequences 29 (2026), Article 26.4.8, Theorem (label T3), lines 460–462, https://cs.uwaterloo.ca/journals/JIS/VOL29/Alzer/alzer22.tex Proves `Wanted` entry `harmonic_partial_sum_not_int`.
