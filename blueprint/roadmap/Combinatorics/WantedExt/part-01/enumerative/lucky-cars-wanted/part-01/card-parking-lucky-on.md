---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted.card_parking_lucky_on
---

# Theorem 4

**Theorem 4**: for disjoint `L, U ⊆ [n]`, the number of
parking functions in which the cars in `L` are lucky and the
cars in `U` are not is
`(∏_{i ∈ L} (n+2-i)) (∏_{i ∈ U} (i-1)) (n+1)^{n-|L|-|U|-1}`
(paper's one-based indices; here `i.val` is one less).

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Combinatorics.Enumerative.LuckyCarsWanted](../../../../../../../sources/v2/WantedExt.md)
- Steve Butler et al., "Lucky Cars and Lucky Spots in Parking Functions", Theorem 4.
