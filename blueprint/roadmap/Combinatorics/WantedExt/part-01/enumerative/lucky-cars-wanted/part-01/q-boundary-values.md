---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted.q_boundary_values
---

# Lemma 9

**Lemma 9**: the boundary values
`q_n(n,j) = \binom{n-1}{j-1} j^{j-2} (n-j+1)^{n-j-1}`,
`q_n(1,j) = ∑_{k=j}^n \binom{n-1}{k-1} k^{k-2} (n-k+1)^{n-k-1}`,
`q_n(i,n) = n^{n-2}`, and
`q_n(i,1) = (n+1)^{n-i-1} n^{i-2} (2n+1-i)`, in zero-based
indices and in `ℚ` for the possibly negative exponents.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Combinatorics.Enumerative.LuckyCarsWanted](../../../../../../../sources/v2/WantedExt.md)
- Steve Butler et al., "Lucky Cars and Lucky Spots in Parking Functions", Lemma 9.
