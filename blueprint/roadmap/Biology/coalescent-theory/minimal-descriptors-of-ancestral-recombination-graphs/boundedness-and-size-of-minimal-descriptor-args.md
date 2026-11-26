# Boundedness and size of minimal descriptor ARGs

Let $G$ be an ancestral recombination graph on $K$ extant samples with $M$ non-mixing segments, possibly with infinitely many vertices (an unbounded history with no grand most recent common ancestor, GMRCA). Then:

1. **Bounded descriptor.** $G$ always has a minimal descriptor with finitely many vertices and a GMRCA.
2. **GMRCA degree.** That GMRCA has degree at most $MK$.
3. **Size bounds.** In any nontrivial minimal descriptor ARG, the numbers $n_c$ of coalescent events, $n_e$ of genetic-exchange events and $n_v$ of non-leaf vertices satisfy

$$1 \le n_c \le M(K-1) + 1, \qquad 0 \le n_e \le K(M-1) + M(K-1), \qquad n_v = O(MK).$$

4. **Bounded degree.** Every minimal descriptor has a bounded number of edges at each vertex, with a bound depending only on $K$ and $M$.
5. **Local overlap.** If a non-GMRCA coalescent vertex of a minimal descriptor has children $u_1, \dots, u_l$ with $l > 1$, then every $u_i$ shares at least one segment with some other $u_j$, $j \ne i$.

## Depends on

- [Minimal descriptor of an ancestral recombination graph](minimal-descriptor-of-an-ancestral-recombination-graph.md)

## Expansion

For (1), first delete every non-t-coalescent coalescent vertex, which preserves trees and samples. The only remaining infinite ancestral chains then start at least common ancestors (LCAs) of the embedded trees, and two such chains cannot meet: a meeting vertex would be a non-GMRCA coalescent vertex that is either not t-coalescent or a common ancestor of two LCAs of the same tree. Replacing the disjoint infinite chains by edges from one new vertex, each labelled by the union of its chain's labels, preserves the samples and makes the new vertex the GMRCA. Each tree has at most $K$ such LCAs, giving (2). For (3), every non-GMRCA coalescent vertex is a coalescence of some marginal tree, and the $M$ trees on $K$ leaves have at most $M(K-1)$ coalescence events in total. Exchange events sit at junctions between adjacent segments: the samples have at most $K(M-1)$ such junctions, and each coalescence event of a marginal tree creates at most one additional junction in the coalescing vertex, adding at most $M(K-1)$. Parida et al. also estimate that for a natural class of ARGs the expected reduction in the number of vertices from $G$ to its minimal descriptor is exponential (their Equation 8), and observe the same empirically, which is what makes sampling algorithms over minimal descriptors cheaper than over full ARGs.

## Sources

- L. Parida, P. F. Palamara, A. Javed, "A minimal descriptor of an ancestral recombinations graph", BMC Bioinformatics 12 (Suppl. 1) (2011), S6, <https://doi.org/10.1186/1471-2105-12-s1-s6> (PMC3044314), Theorem 3, Corollaries 1–2, and Theorem 4 (Equations 1–3).
