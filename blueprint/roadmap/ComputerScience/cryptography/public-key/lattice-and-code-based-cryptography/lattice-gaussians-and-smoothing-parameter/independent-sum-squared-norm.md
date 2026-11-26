# Expected squared norm of a linear combination of independent random vectors

Let $X_1, \dots, X_k$ be independent square-integrable random vectors in a real Hilbert space with $\mathbb{E}\|X_i\|^2 \le l$ and $\|\mathbb{E} X_i\|^2 \le \varepsilon$ for all $i$. Then for every real coefficient vector $z$,

$$\mathbb{E}\Bigl\|\sum_i z_i X_i\Bigr\|^2 \le (l + \varepsilon k)\,\sum_i z_i^2.$$

## Proof sketch

Expand the square: diagonal terms contribute at most $l\sum z_i^2$, and by independence each cross term equals $z_iz_j\langle\mathbb{E}X_i, \mathbb{E}X_j\rangle \le |z_iz_j|\varepsilon$; then $\sum_{i \ne j}|z_iz_j| \le k\sum z_i^2$ by Cauchy–Schwarz.

## Sources

- D. Micciancio and O. Regev, "Worst-Case to Average-Case Reductions Based on Gaussian Measures", SIAM Journal on Computing 37(1), 2007.
