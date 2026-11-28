# Approximate decomposition of WTAP solutions into thin components (Traub-Zenklusen)

Let $(G=(V,E),L,w)$ be a WTAP instance rooted at $r$, and call a link set $C$ $k$-thin if every vertex lies on the paths $P_\ell$ of at most $k$ links $\ell \in C$.

(i) (Decomposition theorem.) Let $F \subseteq L$ be a WTAP solution and let $U$ be a set of up-links whose paths $P_u$, $u \in U$, are pairwise edge-disjoint. For every $\varepsilon > 0$ there are a partition $\mathcal{C}$ of $F$ into $\lceil 1/\varepsilon \rceil$-thin sets and an exceptional set $R \subseteq U$ with $w(R) \le \varepsilon\, w(U)$ such that every $u \in U \setminus R$ satisfies $P_u \subseteq \bigcup_{\ell \in C}P_\ell$ for some $C \in \mathcal{C}$, that is, $u \in \mathrm{Drop}_U(C)$.

(ii) (Computability.) For every constant $k$ and every such $U$, a $k$-thin link set $C$ minimizing $w(C)/w(\mathrm{Drop}_U(C))$ can be computed in polynomial time, by dynamic programming over the tree.

The exceptional set cannot be avoided: there are instances in which covering every up-link of $U$ by one part forces all links of $F$ into a single part that is not $m$-thin, for arbitrarily large $m$ (Traub–Zenklusen, Figure 2).

## Proof sketch

For each $u \in U$ choose, carefully, a minimal set $F_u \subseteq F$ of links whose paths cover $P_u$, ordered along $P_u$; each $F_u$ is $2$-thin. These choices define a dependency graph on $F$, a union of directed paths $(F_u, A_u)$, whose connected components are arborescences, and two links of a component sharing a vertex are in an ancestor relation. Label each $A_u$ by the number of distinct sets $A_{u'}$ met on the path from its component's root, put $k=\lceil 1/\varepsilon \rceil$, and for the residue class $i \bmod k$ of minimum weight let $R$ be the up-links whose label is $\equiv i \pmod k$. Removing their arcs leaves components in which every path meets at most $k-1$ sets $A_u$, which are $k$-thin, and averaging over the $k$ residue classes gives $w(R) \le w(U)/k \le \varepsilon\, w(U)$. Part (ii) is a dynamic program over the rooted tree that tracks, at each vertex, the boundedly many links of the candidate component passing through it.

## Depends on

- [Weighted tree augmentation problem (WTAP)](weighted-tree-augmentation.md)
- [Relative greedy algorithms for weighted tree augmentation](relative-greedy-augmentation.md)

## Sources

- Vera Traub, Rico Zenklusen, "A Better-Than-2 Approximation for Weighted Tree Augmentation", FOCS (2021), arXiv:2104.07114, Theorem 5, Lemma 4, Figures 2 and 4, Sections 4 and 5.
