# Display sets of level-1 networks are hypercubes in the rSPR graph

**Setting.** A rooted binary phylogenetic network $\mathcal N$ on leaf set $X$ with $k$ reticulations *displays* a rooted binary phylogenetic $X$-tree if the tree can be obtained by keeping one incoming arc at each reticulation and suppressing; the **display set** $T(\mathcal N)$ has at most $2^k$ trees. For a set $\mathcal P$ of phylogenetic $X$-trees, the **rSPR graph** has vertex set $\mathcal P$ and an edge between two trees at rooted subtree-prune-and-regraft distance $1$. $Q_k$ is the $k$-dimensional hypercube. A network is **level-1** if its underlying cycles are vertex-disjoint.

For trees $\mathcal T, \mathcal T'$ with $d_{\mathrm{rSPR}} = 1$, a *moving subtree* $X' \subseteq X$ is one whose pruning and regrafting turns $\mathcal T$ into $\mathcal T'$; it is recorded as the ordered pair $(X', Y')$ with $Y'$ the minimal common cluster properly containing $X'$. If the rSPR graph of $\mathcal P$ is isomorphic to $Q_k$, with $E_i$ the edges of the $i$-th coordinate direction, it has the **nested subtree property** if every edge of $E_i$ can be labeled by a common pair $(X_i, Y_i)$ such that for all $i \ne j$ one of the following holds: (I) $Y_i \cap Y_j = \emptyset$; (II) $Y_i \subseteq X_j$; (III) $Y_i \subset Y_j$ and $X_j \cap Y_i = \emptyset$.

**Theorem (maximum display sets).** If $|T(\mathcal N)| = 2^k$ (e.g. $\mathcal N$ normal), then $Q_k$ is a spanning subgraph of the rSPR graph of $T(\mathcal N)$; in particular for $k \ge 2$ the display set can be listed as a cyclic sequence in which consecutive trees differ by one rSPR move (a Hamilton cycle, from a Gray code on reticulation choices).

**Theorem (characterization of level-1 display sets).** A set $\mathcal P$ of phylogenetic $X$-trees is the display set of a level-1 network on $X$ if and only if, for some $k \ge 0$, the rSPR graph of $\mathcal P$ is isomorphic to $Q_k$ and has the nested subtree property. Consequently the rSPR graph of a level-1 network with at least two non-trivial reticulations is Hamiltonian, and if the rSPR graph of $\mathcal P$ is disconnected, no network at all has display set exactly $\mathcal P$.

**Theorem (reconstruction).** An algorithm decides whether $\mathcal P$ is the display set of a level-1 network and, if so, builds one, in time $O(|\mathcal P|^2|X|^2)$. With $n_i$ the number of pairs that can label $E_i$ consistently, there are exactly $\prod_{i=1}^k n_i$ level-1 networks without trivial reticulations whose display set is $\mathcal P$; for adjacent trees the number of moving subtrees is $1$ or $3$, and it is $3$ iff the trees are also one rNNI move apart.

## Depends on

- [Rspr Dist](../../../not-yet-classified/rooted-spragreement-forest/rspr-dist.md)

## Expansion

Each reticulation $v_i$ is a binary switch; flipping one switch prunes the cluster $C(v_i)$ below the reticulation and regrafts it on the other side of its cycle, which is a single rSPR move with moving subtree $X_i = C(v_i)$ and $Y_i = C(u_i)$ the cluster at the top of the cycle. In a level-1 network cycles are disjoint, so switches act independently and their clusters are either disjoint (I), nested inside a reticulation's subtree (II), or nested inside the cycle but off the reticulation path (III); this is exactly the nested subtree property, and conversely the property lets one rebuild the cycles one coordinate at a time. The hypercube structure reflects that a level-1 network displays no trees beyond those required by its input.

## Sources

- Janosch Döcker, Simone Linz and Charles Semple, "Hypercubes and Hamilton cycles of display sets of rooted phylogenetic networks", Advances in Applied Mathematics 152 (2024), 102595, <https://doi.org/10.1016/j.aam.2023.102595>; numbering as in arXiv:2211.06549: Theorem 2.2, Corollary 3.3, Theorem 4.1, Section 5 (moving subtrees and the nested subtree property), Theorem 5.1, Corollary 5.3, Proposition 6.1, Theorem 6.8 and Corollary 6.9.
