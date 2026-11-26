# Censored cluster-size likelihood for negative-binomial offspring

**Model.** In each of several independent locations $i$, an outbreak cluster is started by $s_i \ge 1$ imported cases. Every case independently produces a number of secondary cases drawn from the negative-binomial law with mean $R_0 \ge 0$ and dispersion $k > 0$, and the resulting Galton–Watson process is subcritical or the population is large enough that its total progeny $X$ (including the $s_i$ initial cases) is the cluster size. For integers $x \ge s \ge 1$ the probability that a cluster started by $s$ cases has final size $x$ is

$$c(x; s) = \Pr(X = x; s) = \frac{k s}{k x + x - s} \binom{k x + x - s}{x - s} \frac{(R_0/k)^{x - s}}{(1 + R_0/k)^{k x + x - s}},$$

with the generalized binomial coefficient, and $c(x; s) = 0$ for $x < s$.

**Censored likelihood.** Partition the locations into a set $A$ whose clusters have ended (in the source, no new case for 7 days) and a set $B$ whose clusters are still growing, so that only the lower bound $X \ge x_i$ is known. With observed sizes $x_i$, the likelihood of $(R_0, k)$ is

$$L(R_0, k) = \prod_{i \in A} c(x_i; s_i) \prod_{i \in B} \Big(1 - \sum_{m = 0}^{x_i - 1} c(m; s_i)\Big),$$

where the empty sum (for $x_i = 0$) is $0$. As $k \to \infty$ with $R_0$ fixed, $c(x; s)$ tends to the total-progeny law of a Poisson branching process, which is how the source compares the overdispersed and Poisson models.

## Depends on

- [Negative-binomial offspring probabilities](../../superspreading-and-negative-binomial-offspring/nb-pmf.md)
- [Negative-binomial offspring distribution](../../superspreading-and-negative-binomial-offspring/nb-offspring.md)

## Expansion

By the hitting-time (Dwass) formula, the total progeny of a branching process started from $s$ individuals satisfies $\Pr(X = x) = \frac{s}{x}\Pr(Y_1 + \dots + Y_x = x - s)$ with $Y_j$ i.i.d. offspring counts. A sum of $x$ i.i.d. negative binomials with dispersion $k$ is negative binomial with dispersion $k x$ and the same success probability $k/(k + R_0)$, which gives $\frac{s}{x}\frac{\Gamma(kx + x - s)}{\Gamma(kx)\Gamma(x - s + 1)} \frac{(R_0/k)^{x - s}}{(1 + R_0/k)^{kx + x - s}}$; rewriting $\Gamma(kx + x - s)/\Gamma(kx)$ through the generalized binomial coefficient yields the displayed form. Growing clusters are right-censored observations of $X$, so they contribute survival probabilities rather than point masses. The source fixes $R_0$ on a grid in $[0,5]$ and samples $1/k$ by MCMC under a half-normal prior; with $R_0 = 2.5$ the median estimate is $k \approx 0.1$.

## Sources

- A. Endo, Centre for the Mathematical Modelling of Infectious Diseases COVID-19 Working Group, S. Abbott, A. J. Kucharski and S. Funk, *Estimating the overdispersion in COVID-19 transmission using outbreak sizes outside China*, Wellcome Open Research (2020). <https://doi.org/10.12688/wellcomeopenres.15842.3> (PMCID: PMC7338915). Methods: "Model", "Proportion responsible for 80% of secondary transmissions".
- S. Blumberg and J. O. Lloyd-Smith, *Inference of $R_0$ and transmission heterogeneity from the size distribution of stuttering chains*, PLoS Computational Biology (2013).
