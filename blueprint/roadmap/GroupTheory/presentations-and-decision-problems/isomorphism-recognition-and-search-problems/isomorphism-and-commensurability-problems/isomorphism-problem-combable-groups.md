# The isomorphism problem is unsolvable for combable groups

There is a recursive sequence of finite presentations of combable groups for which no algorithm decides which of the groups are isomorphic to the first one.

A group $\Gamma$ with finite generating set $A$ is combable if there are words $\sigma_\gamma$ over $A^{\pm 1}$, one for each $\gamma \in \Gamma$ and representing it, and a constant $k > 0$ such that for each $\gamma \in \Gamma$ and $a \in A$ the paths in the Cayley graph from the identity labeled $\sigma_\gamma$ and $\sigma_{\gamma a}$ remain uniformly $k$-close (the fellow traveller property). The isomorphism problem is unsolvable in the class of combable groups (Theorem B of the source): there are a finitely generated free group $F(A)$ and a recursive sequence of finite subsets $R_n \subseteq F(A)$ such that each group $\Gamma_n = \langle A \mid R_n \rangle$ is combable, but there is no algorithm deciding which $\Gamma_n$ are isomorphic to $\Gamma_1$.

The groups constructed are neither bicombable nor automatic; for those classes the problem is left open by the source.

## Depends on

- [Group](../../../group-basics/group.md)
- [Cayley digraph](../../../../GraphTheory/algebraic-graph-theory/part-01/directed-cayley-graph.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Novikov–Boone theorem (unsolvability of the word problem)](../../word-problem-for-groups/novikov-unsolvable.md)
- [Serre's Property FA](../../../free-groups/automorphisms-of-free-groups/finite-index-subgroups-of-automorphism-groups-of/has-property-fa.md)

## Expansion

The proof combines the author's construction of combable groups as doubles $\Delta(N \times F; \hat F)$ over graphs of subgroups of products with an encoding of the fact that there is no algorithm deciding which $m$-element subsets generate a direct product of free groups, or certain hyperbolic groups; these generation problems are unsolvable by Mihailova-type fibre product constructions from groups with unsolvable word problem. A group with property FA and a finitely presented group with property $\Psi$ enter the precise statement (Theorem 4.1 of the source).

## Sources

- M. R. Bridson, "The conjugacy and isomorphism problems for combable groups", Mathematische Annalen 327 (2003), no. 2, 305–314, https://doi.org/10.1007/s00208-003-0453-6; read in arXiv:math/0203109v1 (Theorem B in the introduction and Theorem 4.1 of arXiv:math/0203109v1).
