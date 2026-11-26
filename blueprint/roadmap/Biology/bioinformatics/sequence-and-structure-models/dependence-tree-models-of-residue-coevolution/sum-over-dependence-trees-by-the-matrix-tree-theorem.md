# Sum over dependence trees by the matrix-tree theorem

For an alignment with columns $1, \dots, w$, a dependence tree $\pi$ assigns to each column $j$ other than a root $r$ one parent column $\pi(j)$, so that the parent graph is a spanning tree; given $\pi$, the alignment probability is $P(D \mid \pi) = \prod_i P(D_i) \prod_{j \ne r} R_{j\pi(j)}$, independent of the choice of root. With a prior factorizing over edges, $P(\pi) = \prod_{j \ne r} W_{j\pi(j)}$, and $M_{ij} = W_{ij} R_{ij}$, summing over all dependence trees gives

$$P(D) = \prod_i P(D_i) \sum_{\pi} \prod_{j \ne r} M_{j\pi(j)} = \prod_i P(D_i)\, \det Q(L), \qquad L_{ij} = \delta_{ij} \sum_k M_{ik} - M_{ij},$$

where $Q(L)$ is the Laplacian $L$ with one row and the corresponding column removed (Kirchhoff's matrix-tree theorem). The posterior probability that columns $k$ and $l$ are directly coupled is

$$P\bigl((kl) \mid D\bigr) = \frac{P_{kl}(D)}{P(D)}, \qquad P_{kl}(D) = \prod_i P(D_i)\, M_{kl} \sum_{\pi'} \prod_{j \ne r} M_{j\pi'(j)},$$

where $\pi'$ runs over spanning trees of the graph in which $k$ and $l$ are contracted into one node with edge weights $M_{(kl)m} = M_{km} + M_{lm}$, so it is again a ratio of two determinants.

## Depends on

- [Dirichlet-marginal dependence ratio of alignment columns](dirichlet-dependence-ratio-of-alignment-columns.md)

## Proof depends on

- [Weighted matrix-tree theorem](../../../../GraphTheory/algebraic-graph-theory/part-01/effective-resistance-and-electrical-networks/weighted-matrix-tree.md)

## Expansion

The model allows each column to depend on at most one other column, which keeps the number of parameters estimable, and the conditional distributions are integrated out, so only the ratios $R_{ij}$ remain. Summing over all $w^{w-2}$ spanning trees of the complete graph costs only an $O(w^3)$ determinant. Because a spanning tree has exactly $w - 1$ edges, edges compete: a pair whose dependence is explained by a chain of stronger direct dependences (for example two residues each in contact with a third) appears mainly in low-weight trees, so its posterior is small even when its mutual information is large. This removes much of the indirect co-evolution that confounds contact prediction from mutual information. Spanning trees containing a given edge are in bijection with the edge times spanning trees of the contracted graph, which gives the formula for $P_{kl}$. In practice the entries of $M$ span many orders of magnitude and are rescaled monotonically before the determinants are computed.

## Sources

- Burger L, van Nimwegen E. Disentangling direct from indirect co-evolution of residues in protein alignments. *PLoS Computational Biology* (2010), Materials and Methods, "Probabilistic model", "Calculating posteriors" and "Phylogenetic correction", equations (2)–(15) and (27). DOI <https://doi.org/10.1371/journal.pcbi.1000633>. PMCID PMC2793430.
