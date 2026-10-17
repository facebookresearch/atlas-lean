---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibilityWanted.fib_two_mul_prime_odd_and_fib_fib_add_two_mod
---

# Fib two mul prime odd and fib fib add two mod

The paper's Theorem 2: if `p` is an odd prime with
`p % 3 = 2` and `p % 5 = 2` or `3`, and `n = 2 * p` or
`n = 4 * p`, then `Nat.fib n` is odd and
`Nat.fib (Nat.fib n + 2) ≡ 1` modulo `Nat.fib n`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.Recurrences.FibonacciSumDivisibilityWanted](../../../../../../sources/v2/WantedExt.md)
- Oisín Flynn-Connolly, "On the Divisibility of Sums of Fibonacci Numbers", Theorem 2.
