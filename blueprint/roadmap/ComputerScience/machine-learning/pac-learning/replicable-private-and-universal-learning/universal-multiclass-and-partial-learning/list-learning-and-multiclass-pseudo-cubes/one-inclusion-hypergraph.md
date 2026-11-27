# One-inclusion hypergraphs, orientations and out-degree

Let $H \subseteq Y^n$ be a class on $n$ coordinates. Its **one-inclusion hypergraph** $G(H)$ has vertex set $H$ and, for each $i \in [n]$ and each $f : [n] \setminus \{i\} \to Y$ such that $e_{i,f} = \{h \in H : h|_{[n] \setminus \{i\}} = f\}$ is nonempty, a hyperedge $(e_{i,f}, i)$ in direction $i$. An **orientation** is a map $\sigma$ choosing a vertex $\sigma(e) \in e$ for every hyperedge, and the out-degree of $h$ is the number of hyperedges $e \ni h$ with $\sigma(e) \ne h$. Every deterministic transductive learner on $n$ points induces an orientation and conversely; by a leave-one-out symmetrization, an algorithm whose orientations all have maximum out-degree at most $M$ has expected error at most $M/(n+1)$ on $n$ realizable samples.

## Depends on

- [k-pseudo-cubes and the k-DS dimension](k-pseudo-cube.md)

## Sources

- N. Brukhim, D. Carmon, I. Dinur, S. Moran, A. Yehudayoff, "A Characterization of Multiclass Learnability", FOCS (2022), arXiv:2203.01550, Definitions 9 and 11, Algorithm 1 and Proposition 15.
- A. Daniely, S. Shalev-Shwartz, "Optimal Learners for Multiclass Problems", COLT (2014), PMLR 35.
