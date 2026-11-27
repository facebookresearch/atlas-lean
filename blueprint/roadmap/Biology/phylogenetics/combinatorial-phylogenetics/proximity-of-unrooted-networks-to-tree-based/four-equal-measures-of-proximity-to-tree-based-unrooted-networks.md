# Four equal measures of proximity to tree-based unrooted networks

**Setting.** An unrooted phylogenetic network $N$ on leaf set $X$, $|X|\ge2$, is a connected graph whose leaves are labelled by $X$ and whose interior vertices have degree at least three. $N$ is *proper* if every connected component left after removing a cut edge or a cut vertex of $N$ contains a leaf. $N$ is *tree-based* if it has a spanning tree whose leaves are exactly $X$ (a support tree). For a network of level $k$ define:
1. $\ell(N)=\min\{|V^1(T)\setminus X|: T\text{ a spanning tree of }N\}$, the minimum number of non-taxon leaves of a spanning tree;
2. $t(N)$, the minimum number of new leaves that must be attached to edges of $N$ to make it tree-based;
3. $p(N)=k'-|X|+1$, where $k'$ is the minimum length of a sequence of paths $(\pi_1,\dots,\pi_{k'})$ partitioning $V(N)$ such that for $i\ge2$ an endpoint of $\pi_i$ is adjacent to some earlier path;
4. $\tau(N)$, the minimum tier of a support network contained in $N$ (a tier-$0$ support network is a support tree).

**Theorem.** For every proper unrooted phylogenetic network $N$ with $|X|\ge2$,

$$\ell(N)=p(N)=t(N)=\tau(N).$$

In particular $N$ is tree-based iff this common value is $0$.

**Related bounds.** For proper $N$ with $|X|\ge2$, the edge-addition measure satisfies $\tfrac12\ell(N)\le e(N)\le\ell(N)$; the NNI-based measure $m(N)$ satisfies $\ell(N)\le m(N)$; and the level-based measure $\lambda(N)$ satisfies $\lambda(N)\le\tau(N)$, with equality for simple networks.

**Rooted connection.** An unrooted network is tree-based iff it can be rooted at the midpoint of an edge and oriented to give a (possibly degenerate) rooted network that is phylogenetically tree-based; for binary networks the rooted network can be taken binary, and the analogous statement holds for strictly tree-based networks.

## Expansion

The proof is the cycle of inequalities $\ell\le p\le t\le\tau\le\ell$. Attaching the paths of a path partition one at a time to the first path gives a spanning tree with at most $p(N)+|X|$ leaves; a support tree of the network with $t(N)$ added leaves splits into paths between leaves; and a spanning tree with $\ell(N)$ extra leaves yields a support network whose tier counts those leaves. Since deciding whether an unrooted network is tree-based is NP-complete, so is computing any of the four equal measures.

## Sources

- Mareike Fischer and Andrew Francis, "How tree-based is my network? Proximity measures for unrooted phylogenetic networks", arXiv:1906.06163 (2019), Definition 3.1, Theorem 3.2, Theorems 4.1, 4.6 and 4.7, Proposition 4.3, Theorems 6.3 and 6.5 and Corollary 6.4, <https://doi.org/10.48550/arXiv.1906.06163>.
