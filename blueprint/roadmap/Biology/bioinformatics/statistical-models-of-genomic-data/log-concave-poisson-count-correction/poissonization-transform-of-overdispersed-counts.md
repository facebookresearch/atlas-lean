# Poissonization transform of overdispersed counts

Let counts follow the [Poisson log-concave compound model](poisson-log-concave-compound-model-for-read-counts.md) with fitted latent log-concave density $e^{\phi}$, and let $G_\phi$ be the cumulative distribution function of the continuous extension of the compound count distribution. Let $F_\mu$ be the cumulative distribution function of the continuous extension of the Poisson law with rate $\mu > 0$.

**Definition.** The Poissonization transform of a count $x$ is

$$T(x) = F_\mu^{-1}\big(G_\phi(x)\big),$$

a probability integral transform that maps each count to the Poisson quantile of the same level. The target rate $\mu$ is a free parameter; it is set from the median of the fitted latent distribution.

**Properties.** $T$ is nondecreasing, so it preserves the ranking of bases and all joint structure along the genome, and it matches the quantiles of the corrected counts to those of a Poisson distribution, so a downstream method built on a Poisson likelihood is effectively run under the compound log-concave model instead. Because $G_\phi$ has a much heavier upper tail than any Poisson law, $T$ compresses large counts strongly.

**Integer counts.** For tools that require integers, use either flooring, $\lfloor T(x)\rfloor$, or randomized rounding, $\lfloor T(x)\rfloor + \xi$ with $\xi \sim \mathrm{Bernoulli}\big(T(x)-\lfloor T(x)\rfloor\big)$, which is unbiased for $T(x)$.

## Depends on

- [Poisson log-concave compound model for read counts](poisson-log-concave-compound-model-for-read-counts.md)

## Proof depends on

- [Inverse transform sampling](../../../../Probability/distributions/distribution-functions/quantile-function-and-inverse-transform-sampling/inverse-transform-sampling/map-cdf-quantile-restrict-icc.md)

## Proof sketch

If $X$ had a continuous distribution with cumulative distribution function $G$, then $G(X)$ would be uniform on $(0,1)$ and $F^{-1}(G(X))$ would have distribution $F$ exactly; with discrete counts the continuous extensions guarantee only that quantiles and densities are matched, which is what the downstream methods need. Flooring generalizes read de-duplication: at typical DNase-seq depths it maps bases with at most about five reads to one read and larger counts to two, so it nearly coincides with de-duplication at low depth but keeps more signal as depth grows. When a downstream method accepts weighted counts, the fractional values $T(x)$ can be used directly, so that inference inherits the consistency of the maximum-likelihood fit under per-base independence and the log-concave assumption.

## Sources

- T. B. Hashimoto, M. D. Edwards and D. K. Gifford, "Universal count correction for high-throughput sequencing", PLoS Computational Biology 10 (2014), e1003494, Methods "Count adjustment via probability integral transform" and "Rounding schemes", <https://doi.org/10.1371/journal.pcbi.1003494>, PMCID PMC3945112.
