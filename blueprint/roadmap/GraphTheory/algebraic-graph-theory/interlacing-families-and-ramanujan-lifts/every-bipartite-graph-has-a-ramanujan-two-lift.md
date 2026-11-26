# Marcus-Spielman-Srivastava: every graph has a one-sided Ramanujan two-lift

Every $d$-regular graph $G$ has a signing $s$ with $\lambda_{\max}(A_s) \le 2\sqrt{d-1}$. Consequently every $d$-regular bipartite Ramanujan graph has a $2$-lift that is again bipartite Ramanujan, and there exist infinite families of $d$-regular bipartite Ramanujan graphs for every $d \ge 3$, proving the bipartite case of the Bilu-Linial conjecture.

## Proof sketch

In an interlacing family some leaf polynomial has largest root at most the largest root of the average, which equals $\mu_G$ by the Godsil-Gutman lemma; by Heilmann-Lieb that root is at most $2\sqrt{d-1}$. For a bipartite graph $A_s$ has symmetric spectrum, so the one-sided bound bounds all new eigenvalues. Starting from $K_{d,d}$ and iterating gives the infinite family.

## Depends on

- [The Bilu-Linial conjecture on Ramanujan two-lifts](bilu-linial-conjecture.md)
- [Ramanujan graphs and bipartite Ramanujan graphs](ramanujan-graphs-and-bipartite-ramanujan-graphs.md)
- [Two-lifts and signings of a graph](two-lifts-and-signings-of-graphs.md)

## Proof depends on

- [Characteristic polynomials of signings form an interlacing family](characteristic-polynomials-of-signings-form-an-interlacing-family.md)
- [Heilmann-Lieb theorem: real roots of the matching polynomial](heilmann-lieb-theorem.md)
- [Spectrum of a two-lift: old and new eigenvalues](spectrum-of-a-two-lift.md)
- [Common upper interlacing bounds some member's largest root by a weighted sum's](../../../Algebra/zeros-of-polynomials/interlacing-families-of-polynomials/exists-max-real-root-le-weighted-sum-of.md)
- [Bipartite Ramanujan graphs of every degree](../../graph-families-and-operations/expander-graphs/exists-bipartite-ramanujan.md)

## Sources

- Adam W. Marcus, Daniel A. Spielman, Nikhil Srivastava, "Interlacing families I: bipartite Ramanujan graphs of all degrees", Annals of Mathematics 182(1) (2015); arXiv:1304.4132.
