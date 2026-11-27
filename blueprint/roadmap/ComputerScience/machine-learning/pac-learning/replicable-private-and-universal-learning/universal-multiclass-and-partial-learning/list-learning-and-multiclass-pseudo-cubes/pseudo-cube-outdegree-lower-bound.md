# Pseudo-cubes force out-degree at least half their dimension

If $H \subseteq Y^d$ contains a pseudo-cube of dimension $d$ (in particular, if $H$ has DS dimension $d$ on $d$ coordinates), then every orientation $\sigma$ of the one-inclusion hypergraph $G(H)$ has maximum out-degree at least $d/2$. Conversely, if $H \subseteq Y^{d+1}$ has DS dimension at most $d$, then $G(H)$ has an orientation of maximum out-degree at most $d$.

## Proof sketch

In a pseudo-cube $B$ every vertex lies in a hyperedge of size at least $2$ in each of the $d$ directions; summing $|e| - 1 \ge |e|/2$ over the hyperedges of $G(B)$ shows the average out-degree of any orientation of $G(B)$ is at least $d/2$, and restricting an orientation of $G(H)$ to $B$ only decreases out-degrees. For the converse, choose for each hyperedge a vertex whose removal keeps the remaining class free of $(d+1)$-dimensional pseudo-cubes; a Hall-type counting argument on the hypergraph, using that no vertex set of $G(H)$ is a $(d+1)$-dimensional pseudo-cube, yields an orientation in which each vertex loses at most $d$ hyperedges.

## Depends on

- [k-pseudo-cubes and the k-DS dimension](k-pseudo-cube.md)
- [One-inclusion hypergraphs, orientations and out-degree](one-inclusion-hypergraph.md)

## Sources

- N. Brukhim, D. Carmon, I. Dinur, S. Moran, A. Yehudayoff, "A Characterization of Multiclass Learnability", FOCS (2022), arXiv:2203.01550.
