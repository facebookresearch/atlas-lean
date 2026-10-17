---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.Combinatorics.Enumerative.OddFibonacciWanted.card_avoid_321_4123_pos_zero
---

# Proposition 2

**Proposition 2** (count): for `1 ≤ k < n`, the number
of `(321, 4123)`-avoiding permutations of `[n]` with
`σ(k) = 1` is `k * |S_{n-k}(321, 4123)|` (positions and
values 1-based in the paper; here the position is
`j : Fin n` with `σ j = 0`, so `k = j + 1`).

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Combinatorics.Enumerative.OddFibonacciWanted](../../../../../../sources/v2/WantedExt.md)
- Juan B. Gil, Felix H. Xu, and William Y. Zhu, "Odd-Indexed Fibonacci Numbers via Pattern-Avoiding Permutations", Proposition 2.
