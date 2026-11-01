---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibilityWanted.tendsto_iInf_pisanoPeriod_div_atTop
---

# Tendsto i Inf pisano Period div at Top

The paper's Corollary 1: the minimum of `π(n) / n` over
positive `n < N` tends to `0` as `N` tends to infinity. The
finite minimum is written as an infimum indexed by the subtype
of elements of `Finset.Icc 1 (N - 1)`, so out-of-range indices
do not contribute an empty infimum.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.Recurrences.FibonacciSumDivisibilityWanted](../../../../../../sources/v2/WantedExt.md)
- Oisín Flynn-Connolly, "On the Divisibility of Sums of Fibonacci Numbers", Corollary 1.
