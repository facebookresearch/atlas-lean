---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.melham_fibonacci_gibonacci_sum_of_squares
---

# Melham fibonacci gibonacci sum of squares

Melham's Fibonacci-gibonacci sum-of-squares identity.

Concept `jis_dep_be96b0afb535ec80f792ab13`.

Here `G` is a bi-infinite integer-valued gibonacci sequence, the finite range
represents `j = 0, …, 2n - 1`, and `Nat.fib (2 * n)` represents `F_(2n)`.
It follows from `melham_fibonacci_gibonacci_sum_of_squares_general`; the hypotheses
`hG_nonzero` and `hn` are unused and keep the source's shape.
Proves `Wanted` entry `melham_fibonacci_gibonacci_sum_of_squares`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Melham fibonacci gibonacci sum of squares general](melham-fibonacci-gibonacci-sum-of-square.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.MelhamGibonacci](../../../../../sources/v2/MathlibExt.md)
- <https://cs.uwaterloo.ca/journals/JIS/VOL27/Adegoke/adegoke12.tex>, lines 92–103, 877–880, and 1824–1828. Source hash `ebe2bfa5fe4599897b5f3944fbec475e37d8ef74af7d901116b07e8b81ba229b`.
