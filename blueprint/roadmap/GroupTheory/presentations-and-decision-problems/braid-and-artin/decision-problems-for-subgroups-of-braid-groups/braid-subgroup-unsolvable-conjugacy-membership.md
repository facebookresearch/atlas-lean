# Braid groups contain finitely presented subgroups with unsolvable conjugacy and membership problems

For every sufficiently large $n$ there is a finitely presented subgroup $H$ of the braid group $B_n$ whose conjugacy problem is unsolvable and whose membership problem in $B_n$ is unsolvable.

For all $n$ sufficiently large there exists a finitely presented subgroup $H < B_n$ such that (Corollary 7 of the source):

1. the conjugacy problem for $H$ is unsolvable: no algorithm decides, given two elements of $H$ as words in its generators, whether they are conjugate in $H$;
2. the membership problem for $H$ is unsolvable: no algorithm decides, given a word in the generators of $B_n$, whether the element it represents lies in $H$.

The word problem is solvable in every finitely presented subgroup of a braid group, since braid groups are residually finite.

## Depends on

- [Braid group on n strands](../endomorphisms-of-braid-groups/braid-group.md)
- [Membership problem for a subset of a finitely generated group](../../membership-and-equation-problems/submonoid-and-rational-subset-membership/membership-problem-for-a-subset.md)
- [Group](../../../group-basics/group.md)
- [Solvable conjugacy problem for a quotient of a free group](../../decision-problems-in-free-abelianized-extensions/conjugacy-problem-solvable.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Some right-angled Artin group has a finitely presented subgroup with unsolvable conjugacy and membership problems](../subgroups-of-right-angled-artin-groups/raag-subgroup-unsolvable-conjugacy-membership.md)

## Expansion

Bridson proved that some right-angled Artin group $A_2$ contains a finitely presented subgroup $H$ whose conjugacy and membership problems are unsolvable (Theorem 18 of the source, quoting Bridson). By the main theorem of the source and its Corollary 2, every right-angled Artin group embeds in a pure braid group, so $A_2$, and with it $H$, embeds in $B_n$ for every sufficiently large $n$. The conjugacy problem of $H$ concerns $H$ alone. For membership: a word in the generators of $A_2$ is effectively rewritten as a word in the generators of $B_n$, so an algorithm deciding membership in $H$ for elements of $B_n$ would decide membership in $H$ for elements of $A_2$.

## Sources

- S. Kim and T. Koberda, "Anti-trees and right-angled Artin subgroups of braid groups", Geometry & Topology 19 (2015), no. 6, 3289–3306, https://doi.org/10.2140/gt.2015.19.3289; arXiv:1312.6465v4 (Theorem 1, Corollary 2, Corollary 7, and Bridson's theorem as Theorem 18, of arXiv:1312.6465v4).
