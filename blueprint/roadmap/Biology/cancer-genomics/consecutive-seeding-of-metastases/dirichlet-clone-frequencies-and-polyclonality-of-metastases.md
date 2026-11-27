# Dirichlet clone frequencies and polyclonality of metastases

In the [consecutive-seeding model](negative-binomial-clone-sizes-under-consecutive-seeding.md) with influxes $k_1, \dots, k_N > 0$ and $k = \sum_i k_i$, let a metastasis be examined when its total size is $Y = \sum_i Y_i$, where $Y_i$ is the number of its cells descended from clone $i$.

**Clone sizes.** Conditionally on the total $Y$, the clone sizes follow the Dirichlet-multinomial law

$$\Pr(Y_1, \dots, Y_N) = \frac{\prod_{i=1}^{N}\binom{Y_i + k_i - 1}{Y_i}}{\binom{Y + k - 1}{Y}},$$

with generalized binomial coefficients $\binom{a+m-1}{m} = \Gamma(a+m)/(\Gamma(a)\,m!)$. It is the law of the Pólya urn with initial weights $k_i$ in which every drawn cell is returned together with a copy.

**Number of clones.** The number $n$ of clones present ($Y_i > 0$) has mean

$$\bar n = N - \sum_{i=1}^{N}\frac{\binom{Y + k - k_i - 1}{Y}}{\binom{Y + k - 1}{Y}},$$

and the probability that the metastasis is polyclonal is

$$\Pr(n > 1) = 1 - \sum_{i=1}^{N}\frac{\binom{Y + k_i - 1}{Y}}{\binom{Y + k - 1}{Y}}.$$

For $N$ clones with equal small influxes ($k \ll N$) this is approximately $1 - \Gamma(\kappa+1)\, Y^{-\kappa}$ with the clone-adjusted influx $\kappa = k(1 - 1/N)$, so monoclonality is the more likely outcome when $\kappa < 1/\log_2 Y$.

**Clone frequencies.** For a large metastasis the clone frequencies $\gamma_i = Y_i/Y$ follow the Dirichlet law

$$p(\gamma_1, \dots, \gamma_N) = \Gamma(k)\prod_{i=1}^{N}\frac{\gamma_i^{k_i - 1}}{\Gamma(k_i)}$$

on the simplex, with means $\bar\gamma_i = k_i/k$. A single clone has marginal law $\gamma_i \sim \mathrm{Beta}\bigl(k\bar\gamma_i, k(1-\bar\gamma_i)\bigr)$ and variance

$$\operatorname{Var}(\gamma_i) = \frac{\bar\gamma_i(1-\bar\gamma_i)}{1+k},$$

which falls as the total seeding influx $k$ grows.

## Depends on

- [Negative binomial clone sizes under consecutive seeding](negative-binomial-clone-sizes-under-consecutive-seeding.md)
- [Dirichlet distribution](../../../Probability/distributions/continuous/dirichlet-distribution/dirichlet-law/dirichlet-measure.md)

## Proof depends on

- [Negative binomial splitting for random variables](../../../Probability/distributions/discrete/negative-binomial-and-beta-binomial-distribution/negative-binomial-splitting/measure-cond-eq-beta-binomial-pmf.md)
- [Convolution of negative binomial laws with a common $p$](../../../Probability/distributions/discrete/negative-binomial-and-beta-binomial-distribution/negative-binomial-splitting/sum-neg-binomial-pmf-mul.md)
- [Mean of the Dirichlet distribution](../../../Probability/distributions/continuous/dirichlet-distribution/dirichlet-law/lintegral-dirichlet-measure-apply.md)

## Proof sketch

Independent negative binomial variables with a common success probability and shapes $k_i$, conditioned on their sum $Y$, are Dirichlet-multinomial with parameters $(k_1,\dots,k_N)$: the factors $q^{k_i}(1-q)^{Y_i}$ multiply to $q^{k}(1-q)^{Y}$, which cancels against the law of the sum, a negative binomial with shape $k$. The marginal of one coordinate is beta-binomial with parameters $(k_i, k-k_i)$; its probabilities at $0$ and at $Y$ give the formulas for $\bar n$ and $\Pr(n>1)$. As $Y \to \infty$ the Pólya urn proportions converge to a Dirichlet limit, and Dirichlet marginals are beta with the stated variance. The single-clone Beta law is the Balding–Nichols form familiar from population genetics, with $1/(1+k)$ in the role of $F_{ST}$.

## Sources

- A. Heyde, J. G. Reiter, K. Naxerova and M. A. Nowak, "Consecutive seeding and transfer of genetic diversity in metastasis", Proceedings of the National Academy of Sciences of the USA (2019), Results, Eqs. [3]–[6], and SI Appendix, <https://doi.org/10.1073/pnas.1819408116>, PMCID PMC6628640.
