# James–Stein estimator shrinking towards the grand mean

For $x \in \mathbb R^N$ and a known noise variance $\sigma^2 \in \mathbb R$, let $\bar x = \frac1N \sum_j x_j$ and $S = \sum_j (x_j - \bar x)^2$. The James–Stein estimator that shrinks towards the grand mean is

$$\hat\theta_i = \bar x + \Bigl(1 - \frac{(N - 3)\sigma^2}{S}\Bigr)(x_i - \bar x),$$

Efron (2021), equation (3.4), with $\sigma_0^2 = \sigma^2$. When all coordinates are equal, $S = 0$ and the convention $a / 0 = 0$ makes the estimate $x$. For $N = 1$ this is always the case; for $N \ge 2$ it is an event of probability zero when $x$ has a nondegenerate Gaussian law, for example $x \sim \mathcal N_N(\theta, \sigma^2 I)$ with $\sigma^2 > 0$. Efron reads it as the empirical Bayes rule for the prior $\theta_i \sim \mathcal N(M, A)$ with $M$ and $A$ unknown, estimated by $\hat M = \bar x$ and $\hat B = 1 - (N - 3)\sigma_0^2 / S$ (equations (3.9)–(3.14)).

## Background

- [James–Stein estimator](james-stein.md): the version that shrinks towards $0$.

## Sources

- B. Efron, "Empirical Bayes: Concepts and Methods", author's manuscript (2021), https://efron.ckirby.su.domains/papers/2021EB-concepts-methods.pdf.
