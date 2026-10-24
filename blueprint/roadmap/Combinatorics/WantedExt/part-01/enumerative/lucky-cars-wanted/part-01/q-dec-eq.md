---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted.qDec_eq
---

# Lemma 22

**Lemma 22**: `q_n^d(i,j)` in zero-based indices: for
`i + j < n` (the paper's `i + j ≤ n + 1` one-based) it is
the product `((n-i-j)^2 / ((n-i)(n-j))) * C(n-i+j-1, j) *
C(n-j+i-1, i)`, and `0` else.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Combinatorics.Enumerative.LuckyCarsWanted](../../../../../../../sources/v2/WantedExt.md)
- Steve Butler et al., "Lucky Cars and Lucky Spots in Parking Functions", Lemma 22.
