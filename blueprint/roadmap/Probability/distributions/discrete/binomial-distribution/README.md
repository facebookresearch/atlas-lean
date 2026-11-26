# Variance of the binomial distribution

For $n \in \mathbb{N}$ and $p \in [0, 1]$, the binomial law $\operatorname{Bin}(n, p)$, viewed as a probability measure on $\mathbb{R}$ (mass $\binom{n}{k} p^k (1 - p)^{n - k}$ at each $k \in \{0, \dots, n\}$), has variance $n p (1 - p)$. Equivalently, every real random variable whose law is $\operatorname{Bin}(n, p)$ has variance $n p (1 - p)$.

## Idea

A binomial count is the number of successes in $n$ independent trials that each succeed with probability $p$. Each trial contributes variance $p(1 - p)$ and independence makes the variances add, which explains the formula. A direct computation from the law goes through the second factorial moment: the identity $k(k-1)\binom{n}{k} = n(n-1)\binom{n-2}{k-2}$ and the binomial theorem give $\mathbb{E}[X(X-1)] = n(n-1)p^2$. Adding the mean $np$ gives the second moment $\mathbb{E}[X^2] = np(1-p) + (np)^2$, and subtracting $(np)^2$ leaves the variance. The variance is largest at $p = 1/2$ and vanishes at $p = 0$ and $p = 1$, where the count is deterministic.

## Statements

- [Variance of the binomial law](variance-id-map-cast-binomial.md)
- [Variance of a binomial random variable](variance-of-has-law-binomial.md): random-variable form
- [Second moment of the binomial law](integral-sq-map-cast-binomial.md): second moment, used in the proof of the main statement
- [Second moment of a binomial random variable](integral-sq-of-has-law-binomial.md): random-variable form
- [Second factorial moment of the binomial law](integral-mul-sub-one-map-cast-binomial.md): second factorial moment, used for the second moment
- [Second factorial moment of a binomial random variable](integral-mul-sub-one-of-has-law-binomial.md): random-variable form
