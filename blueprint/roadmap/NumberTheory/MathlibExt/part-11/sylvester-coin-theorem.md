---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.sylvester_coin_theorem
---

# Sylvester Coin Theorem

Sylvester's coin theorem: the number of natural numbers not representable as a nonnegative
integer combination of two coprime natural numbers is `(a - 1) * (b - 1) / 2`.

Math notes: `Set.ncard` of the nonrepresentable set; natural subtraction makes the
right-hand side `0` when `a = 0` or `b = 0`, matching the empty gap set under `Coprime`.
Proves `Wanted` entry `sylvester_coin_theorem`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.SylvesterCoinTheorem](../../../../sources/v2/MathlibExt.md)
- J. J. Sylvester on the Frobenius coin problem (1882); the count of gaps is `(a - 1) * (b - 1) / 2` for coprime `a b`.
