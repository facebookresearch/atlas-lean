---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TimeM.karatsuba_time_le_rpow
---

# Karatsuba time le rpow

Karatsuba multiplication of `n ≥ 1` digit numbers costs at most `9 * n^(log₂ 3)`.

## Depends on

- [Karatsuba](karatsuba.md)

## Proof depends on

- [Karatsuba Cost](karatsuba-cost.md)
- [Karatsuba Cost le rpow](karatsuba-cost-le-rpow.md)
- [Karatsuba time](karatsuba-time.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DivideAndConquer.Karatsuba](../../../../../../sources/v2/CSLibExt.md)
