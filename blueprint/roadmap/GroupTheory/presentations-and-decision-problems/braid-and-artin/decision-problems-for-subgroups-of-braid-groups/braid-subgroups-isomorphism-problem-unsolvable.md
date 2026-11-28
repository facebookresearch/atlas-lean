# The isomorphism problem for finitely presented subgroups of braid groups is unsolvable

For every sufficiently large $n$, no algorithm decides whether two finitely presented subgroups of the braid group $B_n$ are isomorphic.

For $n \ge 1$ let $\mathfrak{C}_n$ be the class of finitely presented subgroups of the braid group $B_n$ on $n$ strands. If $n$ is sufficiently large, the isomorphism problem for $\mathfrak{C}_n$ is unsolvable: there is no algorithm that, on input of two members $A, B$ of $\mathfrak{C}_n$, halts and determines whether $A \cong B$ (Corollary 6 of the source).

## Depends on

- [Braid group on n strands](../endomorphisms-of-braid-groups/braid-group.md)
- [Group](../../../group-basics/group.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The isomorphism problem for finitely presented subgroups of some right-angled Artin group is unsolvable](../subgroups-of-right-angled-artin-groups/raag-subgroups-isomorphism-problem-unsolvable.md)

## Expansion

Bridson proved that some right-angled Artin group $A_1$ has unsolvable isomorphism problem for its finitely presented subgroups (Theorem 18 of the source, quoting Bridson). The main theorem of the source says that for every finite graph $\Gamma$ there is a finite tree $T$ such that the right-angled Artin group of $\Gamma$ admits a quasi-isometric group embedding into that of $T$ (Theorem 1), where the source's convention makes two generators commute exactly when the vertices are not adjacent; in the usual convention, with generators commuting along edges, the target is the right-angled Artin group of the complement of $T$, an anti-tree; as a consequence every right-angled Artin group embeds in a pure braid group $P_n < B_n$ for some $n$ (Corollary 2). Since $B_n$ embeds in $B_{n+1}$, $A_1$ embeds in $B_n$ for every sufficiently large $n$, and the finitely presented subgroups of $A_1$ are members of $\mathfrak{C}_n$. This replaces the high-genus mapping class groups of Bridson's argument by braid groups.

## Sources

- S. Kim and T. Koberda, "Anti-trees and right-angled Artin subgroups of braid groups", Geometry & Topology 19 (2015), no. 6, 3289–3306, https://doi.org/10.2140/gt.2015.19.3289; arXiv:1312.6465v4 (Theorem 1, Corollary 2, Corollary 6, and Bridson's theorem as Theorem 18, of arXiv:1312.6465v4).
