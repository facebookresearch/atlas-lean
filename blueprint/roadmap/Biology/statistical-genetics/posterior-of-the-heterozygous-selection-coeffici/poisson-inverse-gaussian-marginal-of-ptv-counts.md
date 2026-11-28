# Poisson–inverse-Gaussian marginal of gene PTV counts

For a gene with neutral expectation $\nu = N U > 0$ (sample size $N$ chromosomes times PTV mutation rate $U$), model the observed PTV count as $n \mid s \sim \mathrm{Poisson}(\nu / s)$, the [balance mean](balance-mean.md), and give the heterozygous selection coefficient an inverse Gaussian prior with mean $\alpha > 0$ and shape $\beta > 0$:

$$p(s; \alpha, \beta) = \sqrt{\frac{\beta}{2\pi s^3}} \exp\!\Big(-\frac{\beta (s - \alpha)^2}{2 \alpha^2 s}\Big), \qquad s > 0 .$$

**Proposition.** For every integer $n \ge 0$, the marginal probability of $n$ is

$$P(n \mid \alpha, \beta; \nu) = \int_0^\infty \frac{e^{-\nu/s} (\nu/s)^n}{n!}\, p(s; \alpha, \beta)\, ds = \frac{1}{n!}\, e^{\beta/\alpha} \sqrt{\frac{2\beta}{\pi \alpha}} \Big(\frac{\nu}{\alpha}\Big)^{n} \Big(\frac{\beta}{\beta + 2\nu}\Big)^{\frac{2n+1}{4}} K_{n + \frac12}\!\Big(\frac{\sqrt{\beta(\beta + 2\nu)}}{\alpha}\Big),$$

where $K_\rho$ is the modified Bessel function of the second kind. The posterior density of $s$ given $n$ is $P(n \mid s; \nu)\, p(s; \alpha, \beta) / P(n \mid \alpha, \beta; \nu)$.

Across genes $i = 1, \dots, G$ with counts $n_i$ and expectations $\nu_i$, Cassa et al. fit $(\alpha, \beta)$ by maximizing $\sum_i \log P(n_i \mid \alpha, \beta; \nu_i)$, separately within terciles of $U$, and report each gene's posterior mean of $s_{\mathrm{het}}$.

## Depends on

- [Mean PTV count at mutation-selection balance](balance-mean.md)
- [Cumulative PTV frequency at heterozygote mutation–selection balance](cumulative-ptv-frequency-at-heterozygote-mutation-selection-balance.md)
- [Posterior of the selection coefficient in the Cassa et al. model](posterior-tail-balance-antitone.md)

## Expansion

Collecting the exponents, the integrand equals $\frac{\nu^n}{n!} \sqrt{\frac{\beta}{2\pi}}\, e^{\beta/\alpha}\, s^{-n-3/2} \exp(-a s - b/s)$ with $a = \beta/(2\alpha^2)$ and $b = (\beta + 2\nu)/2$. The Bessel integral $\int_0^\infty s^{p-1} e^{-a s - b/s}\, ds = 2 (b/a)^{p/2} K_p(2\sqrt{ab})$ for $a, b > 0$, with $p = -(n + \tfrac12)$ and $K_{-p} = K_p$, gives $2\, \big(\alpha^2(\beta+2\nu)/\beta\big)^{-(2n+1)/4} K_{n+1/2}\big(\sqrt{\beta(\beta+2\nu)}/\alpha\big)$, and simplifying the powers of $\alpha$ yields the formula. Because $K_{n+1/2}$ of half-integer order is elementary (a polynomial in $1/z$ times $e^{-z}$), the likelihood is cheap to evaluate. The inverse Gaussian family was chosen over gamma and inverse gamma priors by maximum likelihood; its fitted mode near $s_{\mathrm{het}} \approx 0.005$ reflects a broad distribution of heterozygous fitness costs.

## Sources

- C. A. Cassa, D. Weghorn, D. J. Balick et al., "Estimating the selective effects of heterozygous protein-truncating variants from human exome data", Nature Genetics 49 (2017), Online Methods "Estimation of P(shet)" and "Inference of shet on individual genes", Eqs. (4)–(7), <https://doi.org/10.1038/ng.3831>, PMCID PMC5618255.
