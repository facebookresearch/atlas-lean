# Young's lattice

Young's lattice is the set of all integer partitions, including the empty partition, ordered by containment of their Young diagrams.

**Definition.** A [partition](../../../Combinatorics/tilings-board-placements/tilings-of-the-symmetric-group-by-transpositions/partition-shape.md) of $n \in \mathbb N$ is a finite non-increasing sequence $\pi = (n_1, \ldots, n_t)$ of positive integers with $n_1 + \cdots + n_t = n$; the empty partition has no parts. For partitions $\sigma = (s_1, \ldots, s_r)$ and $\pi = (n_1, \ldots, n_t)$ set

$$
\sigma \le \pi \iff r \le t \text{ and } s_i \le n_i \text{ for all } i \le r,
$$

which says that the Young diagram of $\sigma$ is contained in that of $\pi$. This is a [partial order](../../ordered-sets/partial-order.md) on the set $\mathcal P$ of all partitions, and the ordered set $\mathbf Y = \langle \mathcal P, \le \rangle$ is *Young's lattice*. It is a distributive lattice, graded by the size $|\pi| = n$: $\pi$ covers $\sigma$ exactly when $\sigma \le \pi$ and $|\pi| = |\sigma| + 1$. Transposing Young diagrams gives the conjugate partition $\pi^\partial$, and $\pi \mapsto \pi^\partial$ is an automorphism of $\mathbf Y$.

## Depends on

- [Partially ordered set](../../ordered-sets/partial-order.md)
- [Integer partition as a list of row lengths](../../../Combinatorics/tilings-board-placements/tilings-of-the-symmetric-group-by-transpositions/partition-shape.md)

## Proof depends on

None.

## Expansion

This node states a definition; that containment of Young diagrams is a partial order is immediate from the componentwise description.

## Sources

- Alexander Wires, "Complexity in Young's lattice", *Annals of Pure and Applied Logic* 173(4), 2022, article 103075, doi:[10.1016/j.apal.2021.103075](https://doi.org/10.1016/j.apal.2021.103075); read as arXiv:1907.13360v1, <https://arxiv.org/abs/1907.13360v1>, whose numbering is used: Section 2 ("Preliminaries").
