# Young's lattice

Young's lattice is the set of Young diagrams, the finite lower sets of $\mathbb N \times \mathbb N$, ordered by inclusion; equivalently, the set of all integer partitions ordered by containment of their diagrams.

A *Young diagram* is a finite subset $\mu \subseteq \mathbb N \times \mathbb N$ that is a lower set: if $(i, j) \in \mu$, $i' \le i$ and $j' \le j$, then $(i', j') \in \mu$. Young diagrams are ordered by inclusion, $\mu \le \nu \iff \mu \subseteq \nu$, and the ordered set $\mathbf Y$ of all Young diagrams is *Young's lattice*; it is a distributive lattice, with meet and join given by intersection and union.

Reading off the lengths of the nonempty rows matches Young diagrams with integer partitions, the finite non-increasing sequences $(n_1, \ldots, n_t)$ of positive integers, the empty diagram giving the empty partition. Under this matching, $\sigma = (s_1, \ldots, s_r) \le \pi = (n_1, \ldots, n_t)$ exactly when $r \le t$ and $s_i \le n_i$ for all $i \le r$, and $\mathbf Y$ is graded by the size $|\pi| = n_1 + \cdots + n_t$: $\pi$ covers $\sigma$ exactly when $\sigma \le \pi$ and $|\pi| = |\sigma| + 1$. Transposing diagrams, $(i, j) \mapsto (j, i)$, gives the conjugate partition $\pi^\partial$, and $\pi \mapsto \pi^\partial$ is an order automorphism of $\mathbf Y$.

## Sources

- Alexander Wires, "Complexity in Young's lattice", *Annals of Pure and Applied Logic* 173(4), 2022, article 103075, doi:[10.1016/j.apal.2021.103075](https://doi.org/10.1016/j.apal.2021.103075); read as arXiv:1907.13360v1, <https://arxiv.org/abs/1907.13360v1>, whose numbering is used: Section 2 ("Preliminaries").
