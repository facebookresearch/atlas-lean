# Consistency of Neighbor-Net on circular distances

Let $X$ be a finite set with $n$ elements. A split $\{A, B\}$ is compatible with an ordering $x_1, \dots, x_n$ of $X$ if $A$ or $B$ is an interval $\{x_i, \dots, x_j\}$, and a split system is circular if all its splits are compatible with one ordering. A split weight function $\omega \ge 0$ on the splits induces the distance $d_\omega = \sum_S \omega(S)\,d_S$, where $d_S(x, y) = 1$ if $S$ separates $x$ and $y$ and $0$ otherwise; $d$ is a circular distance if $d = d_\omega$ for some $\omega$ with circular support, and this representation is unique. Bryant, Moulton and Spillner (2007, Theorem 4.1) prove that if the input to Neighbor-Net is a circular distance function $d$, its output is a circular split weight function $\omega$ with $d = d_\omega$; so Neighbor-Net recovers the splits of positive weight and their weights exactly. In particular, given an additive tree distance, it returns the splits of the edges of positive length, that is, the tree with its zero-length edges contracted; it returns the tree itself when every internal edge has positive length, since a zero-length internal edge leaves the distance unchanged. The key step (Theorem 4.2) is that the ordering procedure of Neighbor-Net returns an ordering compatible with $d$, using Theorem 4.8: on a circular distance, a pair minimizing the selection criterion $Q(x, y) = (n - 2)d(x, y) - \sum_z d(x, z) - \sum_z d(y, z)$ is adjacent in at least one ordering compatible with $d$.

## Depends on

- [Split Metric](../../not-yet-classified/split-decomposition/split-metric.md)

## Proof depends on

- [Neighbor-joining Q-criterion](../neighbor-joining/q-criterion.md)

## Expansion

1. Definitions: splits, compatibility with an ordering, circular split systems, split metrics, circular distances, and the uniqueness of their representation.
2. The Neighbor-Net algorithm: agglomeration of clusters with the selection and reduction steps of the ordering procedure, followed by least squares estimation of the weights of the splits compatible with the ordering.
3. Theorem 4.8 and Lemma 4.7: the selection criterion picks a pair adjacent in a compatible ordering.
4. Theorem 4.2 by induction on the number of elements and of clusters, and Theorem 4.1 from the least squares step.
5. The corollary for additive tree distances, with recovery of the tree when every internal edge has positive length.

## Sources

- D. Bryant, V. Moulton and A. Spillner, Consistency of the Neighbor-Net algorithm, Algorithms Mol. Biol. 2 (2007), 8, Section 2 and Theorems 4.1, 4.2 and 4.8. <https://doi.org/10.1186/1748-7188-2-8>
