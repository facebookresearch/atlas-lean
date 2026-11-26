# Quality correction constant for allelic imbalance

For a gene $g$ with total allelic coverage $C_g$, the allelic imbalance (AI) estimate is the fraction of reads from one parental allele. In each coverage bin $B_i$ (bin boundaries $\lceil b^k \rceil$ for a base $b$ slightly above $1$, representative coverage $\hat C_i = \sqrt{\bar C_{i-1}\bar C_i}$), the distribution of pooled AI across genes is modelled as a two-component mixture of symmetric beta-binomials,

$$a_i \sim \frac{\mathrm{BetaBin}(2\hat C_i, \alpha_{ki}, \alpha_{ki})}{2\hat C_i} \quad \text{with probability } \omega_{ki}, \quad k = 1, 2,$$

with $\alpha_{1i} > 1$ (mostly biallelic genes) and $\alpha_{2i} \in (0, 1)$ (strongly imbalanced genes). For a symmetric beta-binomial with $n$ trials, the variance is

$$\Sigma = \frac{n(2\alpha + n)}{4(2\alpha + 1)}, \qquad\text{so with } n = 2\hat C_i: \quad \alpha = \frac{(2\hat C_i)^2 - 4\Sigma}{8\Sigma - 4\hat C_i},$$

which gives the moment-matching M-step of the EM algorithm (with $\Sigma$ the responsibility-weighted variance around the mean $\hat C_i$). Simulating pairs of replicates from the fitted mixture with pure binomial sampling yields the expected distribution of the replicate difference $\Delta\mathrm{AI}$. The **quality correction constant** (QCC) is the constant that best fits, across bins and a fixed set of quantiles $q$, the ratios

$$Q^{\mathrm{obs}}_{q,i} / Q^{\mathrm{exp}}_{q,i}$$

of observed to expected quantiles of $\Delta\mathrm{AI}$. For $M \ge 3$ replicates the QCC is the mean of the $\binom{M}{2}$ pairwise constants. Confidence intervals for AI are then computed by treating the AI of gene $g$ as a binomial proportion with effective coverage $C_g / \mathrm{QCC}^2$.

## Depends on

- [Beta-binomial mass function](../../../../Probability/distributions/discrete/negative-binomial-and-beta-binomial-distribution/beta-binomial/beta-binomial-pmf.md)

## Proof depends on

- [Variance of the beta-binomial law](../../../../Probability/distributions/discrete/negative-binomial-and-beta-binomial-distribution/beta-binomial/variance-beta-binomial.md)

## Proof sketch

The beta-binomial variance follows from $\operatorname{Var} = n\mu(1-\mu)\frac{a + b + n}{a + b + 1}$ with $a = b = \alpha$ and $\mu = 1/2$, and inverting it for $\alpha$ is linear. Because the standard deviation of a binomial proportion scales as $C^{-1/2}$, widening every quantile of the replicate difference by a factor $\mathrm{QCC}$ is equivalent to reducing coverage by $\mathrm{QCC}^2$, which is why the correction is applied as an effective-coverage deflation (implemented with Wilson-score proportion intervals, since $C_g/\mathrm{QCC}^2$ need not be an integer). A value $\mathrm{QCC} = 1$ means replicate libraries agree as well as binomial sampling of reads predicts; real libraries show $\mathrm{QCC} > 1$, so a single library underestimates the uncertainty of AI and inflates calls of differential imbalance. The correction depends only on comparing replicates, not on knowing the true AI of any gene.

## Sources

- A. Mendelevich, S. Vinogradova, S. Gupta, A. A. Mironov, S. R. Sunyaev and A. A. Gimelbrant, "Replicate sequencing libraries are important for quantification of allelic imbalance", *Nature Communications* (2021), Methods Eqs. (3)–(11), <https://doi.org/10.1038/s41467-021-23544-8> (PMC8184992).
