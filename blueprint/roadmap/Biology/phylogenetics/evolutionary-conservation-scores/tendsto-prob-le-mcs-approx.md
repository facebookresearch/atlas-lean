# De Moivre–Laplace for the motif conservation score approximation

Let $P$ be a probability measure, $0 < p < 1$, and let $X_0, X_1, \dots$ be independent, identically distributed real random variables with $X_i \in \{0, 1\}$ almost surely and $\int X_i \, dP = p$. Then for every real $z_0$,

$$P\Bigl(z_0 \le z\Bigl(n, \sum_{i<n} X_i, p\Bigr)\Bigr) \to N(0, 1)\bigl([z_0, \infty)\bigr) \qquad (n \to \infty),$$

where $z$ is the [binomial z-score approximation](mcs-approx.md).
