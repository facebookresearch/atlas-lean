---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TimeM.karatsuba_time_le
---

# Karatsuba time le

Karatsuba's cost on `n` digits is at most `3^(⌈log₂ n⌉ + 1)`, for every input.

## Depends on

- [Karatsuba](karatsuba.md)

## Proof depends on

- [Karatsuba Cost](karatsuba-cost.md)
- [Karatsuba Cost le](karatsuba-cost-le.md)
- [Karatsuba time](karatsuba-time.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DivideAndConquer.Karatsuba](../../../../../../sources/v2/CSLibExt.md)
