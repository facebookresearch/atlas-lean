# W-fence lower bound and M-W matching characterization for maximum covering subtrees

**Setting.** A *rooted almost-binary phylogenetic $X$-network* is a simple DAG $N$ with a unique root $\rho$ (in-degree $0$, out-degree $1$ or $2$), leaves (in-degree $1$, out-degree $0$) in bijection with $X$, and every other vertex of in-degree and out-degree in $\{1,2\}$. A *covering subtree* is a subtree of $N$ with the same root and leaf set; $N$ is *tree-based* if it has one spanning all vertices. Two deviation indices are
- $\eta^*(N)$: the minimum number of vertices of $N$ not covered by a covering subtree (computing it is the Maximum Covering Subtree Problem, MCSP);
- $\delta^*(N)$: the minimum number of leaves that must be attached to make $N$ tree-based.

A *zig-zag trail* is a connected subgraph whose edges can be ordered so that consecutive edges share a head or share a tail; the maximal ones partition the edge set uniquely (the maximal zig-zag trail decomposition). Writing $u > v$ for an arc $u \to v$, a maximal trail is a *crown* ($v_1 < v_2 > \cdots < v_{2k} > v_1$), an *M-fence* ($v_1 < v_2 > \cdots < v_{2k} > v_{2k+1}$, even length), an *N-fence* (odd length) or a *W-fence* ($v_1 > v_2 < \cdots > v_{2k} < v_{2k+1}$, even length). With $V_u(Z)$ and $V_\ell(Z)$ the tails and heads of $Z$,

$$|V_\ell(Z)| - |V_u(Z)| = 1,\ 0,\ -1 \quad\text{for M-fences, crowns/N-fences, W-fences respectively.}$$

Let $\mathcal{M}_N$ and $\mathcal{W}_N$ be the sets of maximal M- and W-fences. Trail $Z_i$ is *above* $Z_j$ if $V_\ell(Z_i) \cap V_u(Z_j) \neq \emptyset$. An *M-W pair* is $(Z_i, Z_j) \in \mathcal{M}_N \times \mathcal{W}_N$ with $Z_i$ above $Z_j$; an *M-W matching* is a non-empty set of M-W pairs using each M-fence and each W-fence at most once, and it is *$\mathcal{W}_N$-saturated* if it has $|\mathcal{W}_N|$ pairs.

**Theorem.** For every rooted almost-binary phylogenetic $X$-network $N$:
1. $N$ is tree-based if and only if $\mathcal{W}_N = \emptyset$, and $\delta^*(N) = |\mathcal{W}_N|$.
2. $\eta^*(N) \ge |\mathcal{W}_N|$; hence $\delta^*(N) \le \eta^*(N)$, and the bound is tight.
3. $\eta^*(N) = |\mathcal{W}_N|$ if and only if $\mathcal{W}_N = \emptyset$ or $N$ admits a $\mathcal{W}_N$-saturated M-W matching.

Since $|\mathcal{W}_N|$ is computable in linear time from the decomposition, MCSP is solvable in linear time on networks with a $\mathcal{W}_N$-saturated M-W matching, a class generalizing tree-based networks (general MCSP needs a min-cost-flow algorithm, cubic time for binary $N$).

## Expansion

In a covering subtree each vertex has in-degree $1$, so inside a maximal trail every covered lower vertex uses exactly one of its incoming trail edges; a covering subtree therefore covers at most $|V_\ell(Z)|$ upper vertices of $Z$, and every W-fence (one more upper than lower vertex) leaves at least one vertex uncovered, giving the lower bound. Conversely, if a W-fence $W$ lies directly below an M-fence $M$ (which has a spare lower vertex), deleting a shared vertex $v \in V_\ell(M) \cap V_u(W)$ merges the two fences into trails without W-fences, so the remaining network is tree-based and only $v$ is missed. A saturated matching lets this be done for every W-fence with distinct M-fences, while without it some W-fence costs at least two missed vertices; the proof is an induction on $|\mathcal{W}_N|$.

## Sources

- T. Suzuki, H. Guo, M. Hayamizu, "Rooted Almost-binary Phylogenetic Networks for which the Maximum Covering Subtree Problem is Solvable in Linear Time", arXiv:2305.15132 (2023), definitions of Sections 2–5, the zig-zag-trail proposition of Section 4, and the lower-bound and equality theorems of Section 5, <https://doi.org/10.48550/arXiv.2305.15132>.
