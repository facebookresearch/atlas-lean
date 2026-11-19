# Left convergence is cut-distance convergence

For graphons $W_n$ and $W$ with values in $[0, 1]$,

$$t(F, W_n) \to t(F, W) \text{ for every simple graph } F \iff \delta_\square(W_n, W) \to 0 .$$

The direction ⇐ is the counting lemma; the direction ⇒ is the inverse counting lemma: if $|t(F, U) - t(F, W)| \le 3^{-k^2}$ for all $F$ on $k \ge 2$ nodes, then $\delta_\square(U, W) \le 22 / \sqrt{\log_2 k}$, proved by sampling.

## Informally uses

- [Counting lemma for graphons](abs-graphon-hom-density-sub-le.md): Borgs et al. deduce Theorem 3.8 from Theorem 3.7, whose part (a) is the counting lemma.

## Sources

- C. Borgs, J. T. Chayes, L. Lovász, V. T. Sós and K. Vesztergombi, "Convergent sequences of dense graphs I: Subgraph frequencies, metric properties and testing", *Adv. Math.* 219 (2008), 1801–1851, arXiv:math/0702004, Theorem 3.8 (final statement) and Theorem 3.7.
