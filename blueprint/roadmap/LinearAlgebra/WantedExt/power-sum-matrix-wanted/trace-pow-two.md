---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.LinearAlgebra.PowerSumMatrixWanted.trace_pow_two
---

# Theorem 1

**Theorem 1**: for any positive integer `m` and
any `2 × 2` real-valued matrix `M`,
`Tr (M ^ (2m)) = 2m * ∑_{r=0}^m (-1)^r *
  (2m - r - 1)! / (r! (2m - 2r)!) *
  (Det M)^r * (Tr M)^(2m - 2r)` and
`Tr (M ^ (2m+1)) = (2m + 1) * ∑_{r=0}^m (-1)^r *
  (2m - r)! / (r! (2m + 1 - 2r)!) *
  (Det M)^r * (Tr M)^(2m + 1 - 2r)`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.LinearAlgebra.PowerSumMatrixWanted](../../../../sources/v2/WantedExt.md)
- Peiran Ding, Yanjun Zhu and Lei Wang, "A New Formula for the Sum of Integer Powers Based on Elementary Matrix Theory", Theorem 1, equations (5) and (6).
