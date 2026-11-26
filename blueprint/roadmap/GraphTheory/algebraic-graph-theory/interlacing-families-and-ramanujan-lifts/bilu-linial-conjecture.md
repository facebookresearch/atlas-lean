# The Bilu-Linial conjecture on Ramanujan two-lifts

The *Bilu-Linial conjecture* asserts that every $d$-regular graph $G$ with $d \ge 2$ has a signing $s$ whose signed adjacency matrix satisfies $\|A_s\| = \max_i |\lambda_i(A_s)| \le 2\sqrt{d-1}$. Degree one must be excluded: the only $1$-regular connected graph is $K_2$, and both of its signings have eigenvalues $\pm 1$, while $2\sqrt{d-1} = 0$. For $d = 2$ the bound holds for every signing. For every $d \ge 3$, a positive answer implies, by iterating $2$-lifts starting from the complete graph $K_{d+1}$, that $d$-regular Ramanujan graphs exist for infinitely many sizes. The one-sided version, $\lambda_{\max}(A_s) \le 2\sqrt{d-1}$, suffices for bipartite graphs, whose spectra are symmetric.

## Depends on

- [Two-lifts and signings of a graph](two-lifts-and-signings-of-graphs.md)
- [Spectrum of a two-lift: old and new eigenvalues](spectrum-of-a-two-lift.md)

## Sources

- Yonatan Bilu, Nathan Linial, "Lifts, discrepancy and nearly optimal spectral gap", Combinatorica 26(5) (2006).
- Adam W. Marcus, Daniel A. Spielman, Nikhil Srivastava, "Interlacing families I: bipartite Ramanujan graphs of all degrees", Annals of Mathematics 182(1) (2015); arXiv:1304.4132 (Theorem 5.5).
