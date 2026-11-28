# Structure of level-1 explainable graphs

Use the definitions of networks, level-$k$, explained graphs $\mathscr G(N,t)$ and the class Lev-1-Ex from [the near-cograph characterization](near-cograph-characterization-of-level-1-explainable-graphs.md). Call a graph Lev-$k$-Ex if it is explained by some $0/1$-labeled level-$k$ network.

**Every graph is explainable at some level (Theorem 3.10).** If $G = (X,E)$ has a subset $Y \subsetneq X$ such that $G - Y$ is a cograph, then $G$ is Lev-$|Y|$-Ex and is explained by a $0/1$-labeled phylogenetic lca-network with $O((|Y|+1)|X|) \subseteq O(|X|^2)$ vertices. In particular every graph is Lev-$k$-Ex for some $k \le |X|$, so explainability by unrestricted labeled networks carries no information; restricting the level is what makes orthology graphs testable.

**Heredity (Proposition 4.14).** $G$ is Lev-1-Ex if and only if $G[W]$ is Lev-1-Ex for every non-empty $W \subseteq V(G)$.

**Closure under substitution (Theorem 4.24).** For vertex-disjoint graphs $H, H'$ and $v \in V(H)$, let $H \odot_v H'$ replace $v$ by $H'$, joining every former neighbor of $v$ to all of $V(H')$. The class Lev-1-Ex is closed under this operation and under disjoint union and join. A graph is Lev-1-Ex if and only if it is generated from single vertices $K_1$ and primitive near-cographs by finitely many joins, disjoint unions and substitutions (a valid atomic expression, Definition 4.25 and Theorem 4.26).

**Perfection (Lemma 4.28, Theorem 4.29).** Lev-1-Ex graphs contain no induced cycle $C_k$ and no induced complement $\overline{C_k}$ for $k \ge 5$; hence they are weakly chordal and therefore perfect.

**Twin-width (Proposition 4.30).** Every Lev-1-Ex graph has twin-width at most $2$, and the bound is attained.

## Expansion

For Theorem 3.10, start from a labeled tree explaining the cograph $G - Y$ and add the vertices of $Y$ one at a time by the grafting construction (Theorem 3.9), each graft creating one new hybrid and raising the level by at most one. Heredity follows because restricting the cluster system of an explaining network to $W$ again gives a closed cluster system satisfying the level-1 property (L) (Lemma 4.13, Theorem 2.12). Substitution closure mirrors modular decomposition: a module of $G$ can be explained by an independent subnetwork hung below the vertex that explains it in the quotient. Perfection uses that long holes and antiholes are primitive and far from being cographs after one vertex deletion, so they are not near-cographs; with heredity they cannot occur.

## Depends on

- [Near-cograph characterization of level-1 explainable graphs](near-cograph-characterization-of-level-1-explainable-graphs.md)

## Sources

- A. Lindeberg, G. E. Scholz, N. Wieseke, M. Hellmuth, "Orthology and Near-Cographs in the Context of Phylogenetic Networks", *Algorithms for Molecular Biology* 20(1) (2025), 19, Definitions 4.23 and 4.25, Lemma 4.13, Lemma 4.28, Theorems 2.12, 3.9, 3.10, 4.24, 4.26 and 4.29, Propositions 4.14 and 4.30, <https://doi.org/10.1186/s13015-025-00285-7> (preprint arXiv:2502.08746).
