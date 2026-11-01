---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibilityWanted.sum_fib_mod_prime_eq_and_not_dvd
---

# Sum fib mod prime eq and not dvd

The paper's Theorem 1: for a prime `p > 5`, the sum of the
first `p` Fibonacci numbers is `1` modulo `p` when
`p % 5 = 1` or `4`, is `p - 2` modulo `p` when `p % 5 = 2` or
`3`, and in particular is not divisible by `p`. These are the
residues forced by the paper's Binet-formula computation.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.Recurrences.FibonacciSumDivisibilityWanted](../../../../../../sources/v2/WantedExt.md)
- Oisín Flynn-Connolly, "On the Divisibility of Sums of Fibonacci Numbers", Theorem 1.
