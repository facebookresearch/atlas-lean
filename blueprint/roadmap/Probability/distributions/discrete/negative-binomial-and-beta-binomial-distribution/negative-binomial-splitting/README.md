# Negative binomial splitting

For $r_1, r_2 > 0$, $0 < p < 1$ and $k, n \in \mathbb{N}$ with $k \le n$,

$$\frac{\mathrm{NB}_{r_1, p}(k) \, \mathrm{NB}_{r_2, p}(n - k)}{\mathrm{NB}_{r_1 + r_2, p}(n)} = \mathrm{BB}(n; r_1, r_2)(k),$$

where $\mathrm{NB}_{r, p}(k) = \frac{r^{(k)}}{k!} p^r (1 - p)^k$ is the negative binomial mass function and $\mathrm{BB}(n; \alpha, \beta)(k) = \binom{n}{k} \alpha^{(k)} \beta^{(n-k)} / (\alpha + \beta)^{(n)}$ the beta-binomial mass function, $x^{(k)}$ denoting the rising factorial. So if $X$ and $Y$ are independent counts on a probability space with laws $\mathrm{NB}_{r_1, p}$ and $\mathrm{NB}_{r_2, p}$, the conditional law of $X$ given $X + Y = n$ is beta-binomial with parameters $n$, $r_1$, $r_2$, and it does not depend on $p$.

## Idea

Negative binomial laws with a common $p$ add: $X + Y$ has law $\mathrm{NB}_{r_1 + r_2, p}$, by a convolution identity that is the Chu–Vandermonde identity for rising factorials. Dividing the joint mass by the mass of the total cancels the factors $p^{r_1 + r_2} (1 - p)^n$ and leaves the beta-binomial mass. This parallels the classical fact that independent Poisson counts, given their total, split binomially; reading each negative binomial count as a Poisson count with a gamma rate, the randomness of the rates turns the binomial split into a beta-binomial one. Because the conditional law does not involve $p$, conditioning on the total removes $p$ as a nuisance parameter when two overdispersed counts are compared.

## Statements

- [Negative binomial splitting](neg-binomial-pmf-mul-div-eq-beta-binomia.md)
- [Negative binomial splitting for random variables](measure-cond-eq-beta-binomial-pmf.md): random-variable form
- [Convolution of negative binomial laws with a common $p$](sum-neg-binomial-pmf-mul.md): convolution of negative binomials, used in the proof of the random-variable form

## Background

- [Negative binomial distribution](../negative-binomial/README.md)
- [Beta-binomial distribution](../beta-binomial/README.md)
