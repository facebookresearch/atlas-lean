# A stackable group with unsolvable word problem

There exists a stackable group with unsolvable word problem; hence stackability, unlike algorithmic stackability, does not imply solvability of the word problem.

Let $G$ be a group with a finite inverse-closed generating set $X$, and let $\Gamma$ be its Cayley graph with directed edges $\vec E$ and directed paths $\vec P$. For a maximal tree $T$ in $\Gamma$, a *flow function* for $T$ is a map $\Phi\colon \vec E \to \vec P$ such that (F1) $\Phi(e)$ has the same initial and terminal vertices as $e$; (F2d) $\Phi(e) = e$ when the undirected edge underlying $e$ lies in $T$; and (F2r) the transitive closure of the relation $e' < e$, defined for $e'$ on the path $\Phi(e)$ where neither $e$ nor $e'$ underlies an edge of $T$, is a well-founded strict partial order, so that there is no infinite descending chain $e_1 > e_2 > \cdots$. It is *bounded* if one constant $k$ satisfies $|\Phi(e)| \le k$ for every $e \in \vec E$. $G$ is *stackable* over $X$ if some maximal tree $T$ of $\Gamma$ admits a bounded flow function; it is *algorithmically stackable* over $X$ if some maximal tree admits a bounded flow function whose stacking map, the map recording the label of $\Phi$ on each edge, has decidable graph, and *autostackable* over $X$ if some maximal tree admits a bounded flow function whose stacking map has synchronously regular graph (Definition 1.1 of the source). Algorithmic stackability implies that the word problem is solvable; without the bound $k$ every finitely generated group would qualify, by sending each edge to the tree path between its endpoints. There exists a stackable group with unsolvable word problem, and hence stackability does not imply algorithmic stackability (Theorem 5.1 of the source).

The source also proves that if $H$ is stackable, $A, B \le H$ are finitely generated and $\psi\colon A \to B$ is an isomorphism, then the HNN extension $H *_\psi$ is stackable (Theorem 4.4), and that stackable groups include groups whose Dehn function is not computable.

## Depends on

- [Solvable word problem](word-problem-solvable.md)
- [Group](../../group-basics/group.md)
- [Cayley digraph](../../../GraphTheory/algebraic-graph-theory/part-01/directed-cayley-graph.md)
- [Spanning tree](../../../GraphTheory/algebraic-graph-theory/part-01/kirchhoff-s-matrix-tree-theorem/is-spanning-tree.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Novikov–Boone theorem (unsolvability of the word problem)](novikov-unsolvable.md)

## Expansion

Let $C = \langle Y \mid R \rangle$ be finitely presented with unsolvable word problem, $H = F(Y) \times F(Y')$, and $A \le H$ the Mihailova subgroup of pairs with the same image in $C$, finitely generated with undecidable membership. The example is the HNN extension $G = H *_A$ with the identity map on $A$, so the stable letter commutes with $A$: $H$, a direct product of free groups, is stackable, HNN extensions of stackable groups along finitely generated associated subgroups are stackable, and undecidable membership in $A$ makes the word problem of the extension unsolvable. A good expansion links pages for Mihailova's theorem and for the source's theorem that HNN extensions of stackable groups along finitely generated associated subgroups are stackable (Theorem 4.4).

## Sources

- S. Hermiller and C. Martínez-Pérez, "HNN extensions and stackable groups", Groups, Geometry, and Dynamics 12 (2018), no. 3, 1123–1158, https://doi.org/10.4171/GGD/467; read in arXiv:1605.06145v1, whose numbering is used here (Definition 1.1, Theorem 4.4 and Theorem 5.1 of arXiv:1605.06145v1).
