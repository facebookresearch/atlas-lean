---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.Combinatorics.Enumerative.RascalNumbersWanted.rascalZ_fleron
---

# Theorem 4

**Theorem 4** (Fleron's recursion):
`R_{n,k} = R_{n-1,k} + R_{n-1,k-1} - R_{n-2,k-1} + 1`,
stated for `0 < k < n` since at `k = 0` or `k = n` the right
side equals `2` while `R_{n,k} = 1`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Combinatorics.Enumerative.RascalNumbersWanted](../../../../../../../sources/v2/WantedExt.md)
- Amelia Gibbs and Brian K. Miceli, "Two Combinatorial Interpretations of Rascal Numbers", Theorem 4.
