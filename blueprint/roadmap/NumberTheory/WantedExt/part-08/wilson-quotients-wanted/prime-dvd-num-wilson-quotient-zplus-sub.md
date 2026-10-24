---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.WilsonQuotientsWanted.prime_dvd_num_wilsonQuotientZPlus_sub_bernoulli_alternating
---

# Prime dvd num wilson Quotient ZPlus sub bernoulli alternating

Morozov's Theorem 6 in corrected form: for an odd prime
`p`, `Z^+(p)` is congruent modulo `p` to
`B_{2(p-1)} - B_{p-1} - ∑ k ∈ [0,p), (-1) ^ k * H_k`, in the
rational sense that `p` divides the numerator of the difference.

This is the congruence obtained by summing the paper's
Equation (7). The printed simplification of the alternating
harmonic sum to `H_{p-1} / 2` is false already at `p = 3`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.WilsonQuotientsWanted](../../../../../sources/v2/WantedExt.md)
- Ivan V. Morozov, "On Quotients of a More General Theorem of Wilson", Theorem 6 and Equation (7).
