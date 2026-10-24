---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.Combinatorics.Enumerative.RascalNumbersWanted.two_mul_sum_choose_mul_rascalZ
---

# Theorem 10

**Theorem 10** (binomial-weighted row sum):
`∑_{k=0}^n \binom{n}{k} R_{n,k} = 2^{n-1} \binom{n}{2} + 2^n`,
with the exponent corrected from the printed `n - 2` (at
`n = 2` the sum is `6`, not `5`), doubled to stay integral
at `n = 0`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Combinatorics.Enumerative.RascalNumbersWanted](../../../../../../../sources/v2/WantedExt.md)
- Amelia Gibbs and Brian K. Miceli, "Two Combinatorial Interpretations of Rascal Numbers", Theorem 10.
