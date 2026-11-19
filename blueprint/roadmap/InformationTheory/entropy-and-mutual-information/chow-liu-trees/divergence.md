# Divergence from the Chow–Liu approximation

Let $\iota$ be a finite set of variables, $X = (X_i)_{i \in \iota}$ a random vector with values in $\prod_i \alpha_i$, each $\alpha_i$ finite, and joint law $P$ (a probability mass function), $\tau$ a dependence forest with parent map $j$, and $P_\tau$ the Chow–Liu approximation of $P$ along $\tau$.
The divergence of $P$ from $P_\tau$ is

$$D(P \| P_\tau) = \sum_x P(x) \log_2 \frac{P(x)}{P_\tau(x)},$$

in bits, the terms with $P(x) = 0$ being $0$; it is the Kullback–Leibler divergence of $P$ relative to $P_\tau$
([Chow–Liu divergence as a Kullback–Leibler divergence](divergence-eq-kl-div.md)).
