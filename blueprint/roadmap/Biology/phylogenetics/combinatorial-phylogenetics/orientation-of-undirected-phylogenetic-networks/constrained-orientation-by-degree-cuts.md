# Constrained orientation of undirected phylogenetic networks by degree cuts

**Setting.** Let $N=(V,E,X)$ be an undirected (possibly nonbinary) phylogenetic network: a connected graph with no loops, no parallel edges and no vertex of degree 2, whose degree-1 vertices are the leaves, bijectively labelled by $X$; every non-leaf vertex therefore has degree at least 3. Fix a distinguished edge $e_\rho\in E$ and a desired in-degree $d^-_N(v)$ for every $v\in V$, with $d^-_N(v)=1$ if $v$ is a leaf and $1\le d^-_N(v)<d_N(v)$ otherwise ($d_N(v)$ the degree). Let $N_\rho$ be $N$ with $e_\rho$ subdivided by a new vertex $\rho\notin V$, the *root*; $N_\rho$ has vertex set $V\cup\{\rho\}$ and $|E|+1$ edges. An *orientation* of $(N,e_\rho,d^-_N)$ directs every edge of $N_\rho$ so that the result is a rooted directed acyclic phylogenetic network with root $\rho$: $\rho$ has in-degree 0 and out-degree 2, each $v\in V$ has in-degree exactly $d^-_N(v)$, leaves have out-degree 0, and no vertex other than $\rho$ has both in-degree 1 and out-degree 1. Only the vertices of $V$ carry prescribed in-degrees; the inserted root $\rho$ does not. (Under the standing assumptions every non-leaf $v\in V$ of in-degree 1 has out-degree $d_N(v)-1\ge2$, so the last condition is automatic.)

A *degree cut* is a pair $(V',E')$ with $V'\subseteq V$ and $E'$ an edge cut of $N_\rho$ such that $\rho$ lies in no component of $N_\rho\setminus E'$ containing a vertex of $V'$, every edge of $E'$ is incident to exactly one vertex of $V'$, and every $v\in V'$ is incident to at least one and at most $d^-_N(v)-1$ edges of $E'$.

**Theorem (characterization and uniqueness).** Under the standing assumptions above, the following hold.

*(1) Characterization.* $(N,e_\rho,d^-_N)$ is orientable if and only if both of the following hold: it has no degree cut, and

$$\sum_{v\in V} d^-_N(v)=|E|+1 .$$

*(2) Uniqueness and complexity.* If $(N,e_\rho,d^-_N)$ is orientable, the orientation is unique, and it can be found (or non-orientability certified) in $O(|E|)$ time.

*(3) Binary case.* For binary $N$ the data reduce to the set $R\subseteq V$ of desired reticulations (in-degree 2). Then $(N,e_\rho,R)$ is orientable if and only if $(N,e_\rho,R)$ has no *reticulation cut* (a degree cut $(R',E')$ with $R'\subseteq R$ and $|R'|=|E'|$) and $|R|=|E|-|V|+1$, the cycle rank of $N$. In that case $N\setminus R$ is a forest.

The same linear-time procedure decides orientability of partly directed networks (some arcs already fixed), and it decides in $O(|E|^2)$ time whether a partly directed network is semi-directed.

## Expansion

Necessity of the count is arc counting: after subdividing $e_\rho$ there are $|E|+1$ arcs, and every arc enters exactly one non-root vertex. A degree cut is a set of vertices separated from the root whose in-arcs are too few to be fed through the cut, so acyclicity fails; this gives necessity of "no degree cut". For sufficiency the algorithm grows the oriented part from $\rho$: a vertex is *activated* once it has received its desired number of in-arcs, and its remaining incident edges are then directed outward. If the process stalls before all edges are directed, the stalled frontier is a degree cut. Because every step is forced, the orientation is unique, which is why prescribing the root edge and the in-degrees removes all freedom. In the binary case the in-degree map is determined by $R$, and the count becomes $|R|=|E|-|V|+1$.

## Sources

- K. T. Huber, L. van Iersel, R. Janssen, M. Jones, V. Moulton, Y. Murakami, C. Semple, "Orienting undirected phylogenetic networks", arXiv:1906.07430 (2019), Section "Orienting an undirected phylogenetic network given the root and the desired in-degrees": Definitions 1 and 2, Theorems 1, 2 and 3, Proposition 2, Corollaries 1, 2 and 3, <https://doi.org/10.48550/arXiv.1906.07430>.
