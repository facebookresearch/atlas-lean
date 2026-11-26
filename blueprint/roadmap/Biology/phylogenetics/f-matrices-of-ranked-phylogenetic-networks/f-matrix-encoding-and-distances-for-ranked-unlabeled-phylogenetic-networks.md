# F-matrix encoding and distances for ranked unlabeled phylogenetic networks

**Setting.** A rooted, ranked, unlabeled phylogenetic network with $n$ leaves and $m$ hybridizations has its $n + 2m$ event times totally ordered, $u_1 > u_2 > \cdots > u_{n+2m}$, from the root (one lineage) through branchings (one lineage becomes two) and hybridizations (two lineages merge into one) to the isochronously sampled tips at $u_{n+2m}$. Its *F-matrix* is the $(n+2m)\times(n+2m)$ lower-triangular integer matrix with $F_{i,j}$ = the number of branches present in $(u_j, u_{j-1})$ that neither branch nor hybridize during $(u_i, u_{j-1})$.

**Definition (the space $\mathcal{F}_{n,m}$).** $F$ is an F-matrix if
1. the first row and column are $(1, 0, \dots, 0)$;
2. $F_{2,2} = 2$, $F_{3,3} = 3$, $F_{n+2m,n+2m} = n$, and $F_{i,i} = F_{i-1,i-1} \pm 1 > 0$ ($+1$ at a branching, $-1$ at a hybridization);
3. $F_{i+1,i} = F_{i,i} - 1$ if $F_{i+1,i+1} = F_{i,i} + 1$, and $F_{i+1,i} = F_{i,i} - 2$ if $F_{i+1,i+1} = F_{i,i} - 1$;
4. $F_{3,2} = 1$ and the second column is $1$ down to some row $k$ and $0$ below;
5. every other entry satisfies
$$\max\{0,\ F_{i-1,k} - 2,\ F_{i,k-1},\ F_{i,k-1} + F_{i-1,k} - F_{i-1,k-1} - 2\} \le F_{i,k} \le \min\{F_{i-1,k},\ F_{i,k-1} + 2,\ F_{i,k-1} + F_{i-1,k} - F_{i-1,k-1}\}.$$

**Theorem (bijection).** The map from network topologies to F-matrices is a bijection between rooted ranked unlabeled phylogenetic networks with $n$ leaves and $m$ hybridizations and $\mathcal{F}_{n,m}$. For example, there are exactly $11$ such networks with $n = 3$, $m = 1$.

**Distances.** For two networks with the same $(n,m)$,
$$d_1(F^{(1)}, F^{(2)}) = \sum_{i,j}\big|F^{(1)}_{i,j} - F^{(2)}_{i,j}\big|, \qquad d_2(F^{(1)}, F^{(2)}) = \Big(\sum_{i,j}\big(F^{(1)}_{i,j} - F^{(2)}_{i,j}\big)^2\Big)^{1/2}$$
are metrics on topologies (they inherit the norm axioms through the bijection). Weighting entries by inter-event times, $F_{i,j}W_{i,j}$, gives metrics on timed networks; padding schemes extend them to different numbers of hybridizations and to heterochronous sampling.

## Depends on

- [F-matrix bijection for fully heterochronous ranked tree shapes](../f-matrices-of-heterochronous-ranked-tree-shapes/f-matrix-bijection-for-fully-heterochronous-ranked-tree-shapes.md)

## Expansion

As for ranked trees, the diagonal records lineages through time, now decreasing by one at each hybridization, while off-diagonal entries count lineages persisting across longer intervals. Moving the interval's later endpoint by one event either keeps every lineage or removes those touched by that event, at most two for a hybridization, which explains the widened bounds ($\pm 2$) compared with trees. Reading the differences between neighboring entries identifies, event by event, which existing lineages branch or merge, so the network can be reconstructed and the encoding is bijective; enumerating admissible matrices row by row enumerates networks.

## Sources

- J. Wang, J. A. Palacios and C. Solís-Lemus, "Matrix representations and distance metrics for unlabeled ranked phylogenetic networks", arXiv:2606.08409 (2026), Definition of F-matrices in Section 3, Theorem 3.2 and Section 4, <https://doi.org/10.48550/arXiv.2606.08409>.
