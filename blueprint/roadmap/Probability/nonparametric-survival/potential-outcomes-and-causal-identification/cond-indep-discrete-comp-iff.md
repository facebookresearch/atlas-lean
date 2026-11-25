# Characterisation of balancing scores

Let $\mu$ be a finite measure on $\Omega$, $T$ a measurable event, $X$ a measurable covariate with values in a finite set $\mathcal X$ with measurable singletons, and $b$ any function on $\mathcal X$. Then $T$ is [conditionally independent](cond-indep-discrete.md) of $X$ given $b(X)$ if and only if $b$ is finer than the [propensity score](propensity.md) on values of positive mass: for all $x, x'$ with $\mu(X = x) \ne 0$, $\mu(X = x') \ne 0$ and $b(x) = b(x')$, one has $e(x) = e(x')$. The case $b = e$ is the [balancing property of the propensity score](cond-indep-discrete-propensity.md).

## Sources

- Paul R. Rosenbaum and Donald B. Rubin, *The central role of the propensity score in observational studies for causal effects*, Biometrika 70 (1983), no. 1, 41–55, DOI 10.1093/biomet/70.1.41, Theorem 2.
