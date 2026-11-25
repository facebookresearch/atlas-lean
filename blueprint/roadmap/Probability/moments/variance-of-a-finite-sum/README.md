# Variance of a finite sum

For finitely many square-integrable real random variables $X_1, \dots, X_n$, on a probability space or more generally on
a space with a finite measure $\mu$,

$$\operatorname{var}(X_1 + \dots + X_n) = \sum_{i=1}^n \sum_{j=1}^n \operatorname{cov}(X_i, X_j),$$

where, with $EY = \int Y \, d\mu$, $\operatorname{var}(Y) = E\big((Y - EY)^2\big)$ and
$\operatorname{cov}(Y, Z) = E\big((Y - EY)(Z - EZ)\big)$.

## Idea

Expanding the square of $\sum_i (X_i - EX_i)$ and taking expected values gives the formula. The diagonal terms are the
variances, so
$\operatorname{var}(X_1 + \dots + X_n) = \sum_i \operatorname{var}(X_i) + 2 \sum_{i < j} \operatorname{cov}(X_i, X_j)$,
and for uncorrelated random variables, independent ones among them, the variance of the sum is the sum of the variances.
Without that hypothesis variances need not add: if $X_2 = X_1$ and $\operatorname{var}(X_1) = 1$, then
$\operatorname{var}(X_1 + X_2) = 4$. With Chebyshev's inequality, the formula proves the L² weak law of large numbers.

## Statements

- [Variance of a finite sum](variance-sum.md)

## Background

- [Expected value](../../foundations/laws-of-random-variables-and-identical-distribut/expectation/README.md): expected values

## Sources

- R. Durrett, *Probability: Theory and Examples*, 5th ed., Theorem 2.2.1 and its proof, which expands the variance of a
  sum into covariances (version read: the author's January 2019 PDF).
