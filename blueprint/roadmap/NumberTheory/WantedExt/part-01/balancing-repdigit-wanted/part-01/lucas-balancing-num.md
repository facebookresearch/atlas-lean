---
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.lucasBalancingNum
---

# Lucas Balancing Num

The Lucas-balancing numbers in the indexing of Integers 2025, A15, defined
by `C_0 = 3`, `C_1 = 1` and `C_{n+2} = 6 C_{n+1} - C_n`.

This indexing is forced by the values displayed in the paper's Theorem 3,
`C_2 = 3` and `C_3 = 17` (thus the paper's `C_n` for `n ≥ 1` is the usual
Lucas-balancing number `c_{n-1}` with `c_0 = 1`, `c_1 = 3`).

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.BalancingRepdigitWanted](../../../../../../sources/v2/WantedExt.md)
- Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Theorem 3.
