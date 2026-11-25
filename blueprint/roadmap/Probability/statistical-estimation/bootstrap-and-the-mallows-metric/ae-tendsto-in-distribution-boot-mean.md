# Almost sure validity of the bootstrap for the mean

Let $X_0, X_1, \dots$ be pairwise independent, identically distributed, square-integrable real random variables on a probability space with variance $\sigma^2$, and for a realized data sequence $x = (X_i(\omega))_i$ let $\bar x_n$ be the sample mean and $\bar x^*_n$ the bootstrap mean under the bootstrap world of $x$ (independent draws from the empirical distributions of $x_0, \dots, x_{n-1}$). Then for almost every $\omega$, under the bootstrap world of $x$, $\sqrt n\,(\bar x^*_n - \bar x_n)$ converges in distribution to $\mathcal N(0, \sigma^2)$, the limit law of $\sqrt n\,(\bar X_n - \mathbb{E}X_0)$.

## Sources

- P. J. Bickel and D. A. Freedman, "Some asymptotic theory for the bootstrap", *Annals of Statistics* 9 (1981), 1196–1217.
