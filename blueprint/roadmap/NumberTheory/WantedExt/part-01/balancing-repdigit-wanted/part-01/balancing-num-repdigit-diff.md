---
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.balancingNum_repdigitDiff
---

# Balancing Num repdigit Diff

If `B_k` is a difference of two repdigits then `B_k ∈ {6, 35}`; the paper displays
`B_2 = 6 = 11 - 5` and `B_3 = 35 = 44 - 9`.

The hypothesis `2 ≤ k` is included because `B_1 = 1 = 2 - 1` is also a
difference of two repdigits but is not in the paper's list; with `k ≥ 2` the
statement was verified computationally for `k ≤ 9`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.BalancingRepdigitWanted](../../../../../../sources/v2/WantedExt.md)
- Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Theorem 2 (`integers-2025-A15-thm-2`).
