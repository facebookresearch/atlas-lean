# Marcus-Spielman-Srivastava: every graph has a one-sided Ramanujan two-lift

Every graph $G$ has a signing $s$ such that every eigenvalue of $A_s$ is at most the spectral radius $\rho(T)$ of the universal cover $T$ of $G$. In particular, every $d$-regular graph with $d \ge 2$ has a signing with $\lambda_{\max}(A_s) \le 2\sqrt{d-1}$ (for $d = 1$ the bound fails: every signing of $K_2$ has eigenvalues $\pm 1$). Consequently, for $d \ge 3$, every $d$-regular bipartite Ramanujan graph has a $2$-lift that is again bipartite Ramanujan, which proves the bipartite case of the Bilu-Linial conjecture and gives an infinite family of $d$-regular bipartite Ramanujan graphs for every $d \ge 3$.

## Proof sketch

In an interlacing family some leaf polynomial has largest root at most the largest root of the average, which equals the matching polynomial $\mu_G$ by the Godsil-Gutman lemma; by Heilmann-Lieb its roots are at most $\rho(T)$, which is at most $2\sqrt{d-1}$ for a $d$-regular graph with $d \ge 2$. For a bipartite graph $A_s$ has symmetric spectrum, so the one-sided bound bounds all new eigenvalues in absolute value. Starting from $K_{d,d}$, whose nontrivial eigenvalues are $0$, and iterating gives infinite families of $d$-regular bipartite Ramanujan graphs for every $d \ge 3$.

## Depends on

- [The Bilu-Linial conjecture on Ramanujan two-lifts](bilu-linial-conjecture.md)
- [Ramanujan graphs and bipartite Ramanujan graphs](ramanujan-graphs-and-bipartite-ramanujan-graphs.md)
- [Two-lifts and signings of a graph](two-lifts-and-signings-of-graphs.md)

## Proof depends on

- [Characteristic polynomials of signings form an interlacing family](characteristic-polynomials-of-signings-form-an-interlacing-family.md)
- [Heilmann-Lieb theorem: real roots of the matching polynomial](heilmann-lieb-theorem.md)
- [Spectrum of a two-lift: old and new eigenvalues](spectrum-of-a-two-lift.md)
- [Common upper interlacing bounds some member's largest root by a weighted sum's](../../../Algebra/zeros-of-polynomials/interlacing-families-of-polynomials/exists-max-real-root-le-weighted-sum-of.md)

## Sources

- Adam W. Marcus, Daniel A. Spielman, Nikhil Srivastava, "Interlacing families I: bipartite Ramanujan graphs of all degrees", Annals of Mathematics 182(1) (2015); arXiv:1304.4132 (Theorems 5.3 and 5.5).
