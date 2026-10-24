---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TimeM.karatsubaCost_two_pow
---

# Karatsuba Cost two pow

At `n = 2^k` digits the cost is exactly `3^(k+1) - 2^(k+1)`, that is
`3 * n^(log₂ 3) - 2 * n`.

## Depends on

- [Karatsuba Cost](karatsuba-cost.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DivideAndConquer.Karatsuba](../../../../../../sources/v2/CSLibExt.md)
