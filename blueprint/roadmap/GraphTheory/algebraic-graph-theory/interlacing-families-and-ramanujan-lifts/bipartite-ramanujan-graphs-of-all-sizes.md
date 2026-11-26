# Marcus-Spielman-Srivastava: bipartite Ramanujan graphs of every degree and every size

For every $d \ge 3$ and every $n \ge 1$ there exists a $d$-regular bipartite Ramanujan (multi)graph with $n$ vertices on each side. It can be taken to be a union of $d$ perfect matchings between the two sides.

## Proof sketch

Take the union of $d$ independent uniformly random perfect matchings. The expected characteristic polynomial of a regular graph plus a random permutation of another is a finite free convolution, so the expected characteristic polynomial of the union is a $d$-fold finite free convolution of the characteristic polynomials of single matchings, real-rooted and forming an interlacing family over the choices of permutations. The finite free root bound with optimized $\alpha$ places all nontrivial roots below $2\sqrt{d-1}$, so some outcome achieves it.

## Depends on

- [Finite free convolution preserves real-rootedness and obeys a root bound](finite-free-convolution-preserves-real-rootedness.md)
- [Marcus-Spielman-Srivastava: every graph has a one-sided Ramanujan two-lift](every-bipartite-graph-has-a-ramanujan-two-lift.md)
- [Ramanujan graphs and bipartite Ramanujan graphs](ramanujan-graphs-and-bipartite-ramanujan-graphs.md)

## Proof depends on

- [Finite free convolution preserves real-rootedness and obeys a root bound](finite-free-convolution-preserves-real-rootedness.md)
- [Marcus-Spielman-Srivastava: every graph has a one-sided Ramanujan two-lift](every-bipartite-graph-has-a-ramanujan-two-lift.md)
- [Ramanujan graphs and bipartite Ramanujan graphs](ramanujan-graphs-and-bipartite-ramanujan-graphs.md)

## Sources

- Adam W. Marcus, Daniel A. Spielman, Nikhil Srivastava, "Interlacing families IV: bipartite Ramanujan graphs of all sizes", SIAM Journal on Computing 47(6) (2018), FOCS (2015); arXiv:1505.08010.
