# Variance of a finite sum

Let $\mu$ be a finite measure on a measurable space $\Omega$, and let $X_i$, $i \in \iota$, be finitely many real
functions in $L^2(\mu)$: each is almost everywhere strongly measurable with $\int X_i^2 \, d\mu < \infty$. Then

$$\operatorname{Var}\Big(\sum_{i \in \iota} X_i\Big) = \sum_{i \in \iota} \sum_{j \in \iota} \operatorname{cov}(X_i, X_j),$$

where, with $EY = \int Y \, d\mu$, $\operatorname{Var}(Y) = E\big((Y - EY)^2\big)$ and
$\operatorname{cov}(Y, Z) = E\big((Y - EY)(Z - EZ)\big)$.
