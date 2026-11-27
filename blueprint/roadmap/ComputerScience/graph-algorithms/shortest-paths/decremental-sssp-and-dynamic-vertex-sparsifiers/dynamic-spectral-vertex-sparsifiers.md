# Durfee-Gao-Goranci-Peng: fully dynamic spectral vertex sparsifiers and all-pairs effective resistances

There is a data structure maintaining a $(1 \pm \varepsilon)$ spectral vertex sparsifier with respect to a terminal set of the algorithm's choice under edge insertions, edge deletions and terminal additions, all in sublinear time. As applications, against an oblivious adversary and with high probability:

1. fully dynamic all-pairs effective resistance with $(1 \pm \varepsilon)$-approximate answers in expected amortized update and query time $\tilde O(\min\{m^{3/4}, n^{5/6}\varepsilon^{-2}\}\,\varepsilon^{-4})$ on unweighted graphs; on weighted graphs $\tilde O(m^{5/6}\varepsilon^{-4})$ (Theorem 4.15), and $\tilde O(n^{5/6}\varepsilon^{-6})$ when the edge weights are polynomially bounded, that is, after rescaling the ratio of the largest to the smallest weight is at most polynomial in $n$, since this $n$-based bound runs the weighted structure on a dynamic spectral sparsifier whose guarantee (Lemma 2.4) requires polynomially bounded weights;
2. for unweighted bounded-degree multigraphs with $m$ edges and $m^{-1} < \varepsilon < 1$, under edge insertions and deletions and changes of two entries of a demand vector $b$ that keep $b$ in the range of the Laplacian $L$: a query returning one coordinate $\tilde x(u)$ of a vector $\tilde x$ with $\|\tilde x - L^\dagger b\|_L \le \varepsilon \|L^\dagger b\|_L$, in $\tilde O(n^{11/12}\varepsilon^{-5})$ expected amortized time per operation; and a query returning the energy of the electrical flow routing $b$ within relative error $\varepsilon$, in $\tilde O(m^{5/6}\varepsilon^{-25/6})$ expected amortized time per operation.

## Proof sketch

The Schur complement equals the expected sum of terminal-to-terminal random-walk segments: each walk from a terminal stopped at the next terminal contributes an edge. Sampling such walks gives a sparse unbiased estimator, and terminals are chosen at random so that walks are short and local. An edge update affects only the walks through it, which are resampled, and every update endpoint is made a terminal, so recourse stays small; a query adds its two vertices as terminals and solves on the small sparsifier.

## Depends on

- [Oblivious and adaptive adversaries; amortized and worst-case update time](../../../data-structures/disjoint-sets-and-dynamic-trees/fully-dynamic-connectivity-and-spanning-forests/adversary-and-update-time-models.md)
- [Effective resistance](../../../../GraphTheory/algebraic-graph-theory/part-01/effective-resistance-and-electrical-networks/effective-resistance.md)
- [Schur complements of graph Laplacians onto terminal sets and spectral vertex sparsifiers](laplacian-schur-complement-onto-terminals.md)

## Proof depends on

- [Spectral sparsification by effective-resistance sampling](../../graph-algorithm-bounds/spectral-sparsification-by-effective-resistance.md)
- [Laplacian Schur complements are Laplacians and preserve terminal effective resistances](schur-complement-preserves-resistances.md)

## Sources

- David Durfee, Yu Gao, Gramoz Goranci, Richard Peng, "Fully Dynamic Spectral Vertex Sparsifiers and Applications", STOC (2019), arXiv:1906.10530, Theorems 1.2, 1.3 and 4.15, Lemma 2.4 and Section 1.
