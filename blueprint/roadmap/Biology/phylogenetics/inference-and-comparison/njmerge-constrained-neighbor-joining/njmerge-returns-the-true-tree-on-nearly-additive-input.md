# NJMerge returns the true tree on nearly additive input

**Agreement.** A tree $T'$ on leaf set $R \subseteq S$ agrees with a tree $T$ on $S$ if restricting $T$ to $R$ and suppressing degree-two vertices gives a tree isomorphic to $T'$.

**NJMerge.** The input is a distance (dissimilarity) matrix $D$ on $S = \{s_1, \dots, s_n\}$ and a set $\mathcal T = \{T_1, \dots, T_k\}$ of unrooted binary trees on pairwise disjoint leaf sets $S_1, \dots, S_k$ with $S = \bigcup_i S_i$. NJMerge runs neighbor joining with the usual Saitou–Nei updates of $D$ and of the $Q$-matrix, but at each iteration scans the candidate pairs in increasing order of $Q$ and accepts the first pair $(x, y)$ such that (i) if $x$ and $y$ lie in a common constraint tree they are siblings there, and (ii) replacing $x$ and $y$ by a new leaf $z = (x, y)$ in every constraint tree keeps every pair of constraint trees compatible. After a join the constraint trees are relabeled. If NJMerge returns a tree, that tree agrees with every $T_i$ (it is a compatibility supertree of $\mathcal T$); the pairwise-compatibility heuristic can, however, fail to return a tree.

**Nearly additive matrix.** Let $T$ be a tree with positive edge weights and leaves $1, \dots, n$. A matrix $M$ is nearly additive for $T$ if $|M[i,j] - d_T(i,j)| < \tfrac12 \min_e w_e$ for all $i, j$, where $d_T$ is the path-length metric of $T$ and the minimum is over the branch lengths of $T$.

**Theorem 3.** Let $T^*$ be a tree on $S$, let $D$ be nearly additive for $T^*$, and let every $T_i \in \mathcal T$ agree with $T^*$. Then NJMerge applied to $(\mathcal T, D)$ returns $T^*$.

## Depends on

- [Atteson's theorem: neighbor joining has sup-norm radius one half](../../atteson-s-theorem-on-neighbor-joining/nj-run-splits-of-abs-sub-lt.md)

## Expansion

By Atteson's theorem, unconstrained neighbor joining on a nearly additive matrix for $T^*$ returns $T^*$. Every pair it proposes for joining is a cherry of the current contracted tree $T^*$; since every constraint tree agrees with $T^*$, joining such a pair never separates siblings of a constraint tree and keeps all relabeled constraint trees agreeing with $T^*$, hence pairwise compatible. So the first pair in $Q$-order, which is the pair neighbor joining would choose, is always accepted, and NJMerge reproduces the unconstrained run. The constraint trees need not appear as clades of the output: two caterpillars on $\{A,C,E,G\}$ and $\{B,D,F,H\}$ are both compatible with the caterpillar on $A, \dots, H$ in alphabetical order. Checking whether a set of relabeled trees is compatible is easy because they can be rooted at the new leaf $z$, and rooted compatibility is polynomial.

## Sources

- E. K. Molloy and T. Warnow, "Statistically consistent divide-and-conquer pipelines for phylogeny estimation using NJMerge", Algorithms for Molecular Biology 14 (2019) 14, Definitions 1–2 and Theorem 3, <https://doi.org/10.1186/s13015-019-0151-x>, PMCID PMC6642500.
