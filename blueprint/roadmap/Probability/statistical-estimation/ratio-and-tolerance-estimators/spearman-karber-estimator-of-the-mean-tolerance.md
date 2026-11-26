# Discretization error of the Spearman–Kärber estimator of the mean tolerance

In a bioassay with binary response, the probability of response at dose $x$ is read as the distribution function $F(x)$ of a latent tolerance distribution, an individual's tolerance being the smallest dose that produces a response. The Spearman–Kärber method estimates the mean of the tolerance distribution nonparametrically: the observed response proportions at the doses tested are taken as an empirical distribution function, differencing gives an empirical probability mass function, and the estimate is the mean $\sum x f(x)$ of that discrete distribution; when the observed proportions do not reach $0$ and $1$, the common practice is to assume no response at the next lower dose and complete response at the next higher dose (Siev, Section 3.1). With doses $x_1 < \dots < x_k$ and proportions $p_1 = 0 \le p_2 \le \dots \le p_k = 1$, and the mass $p_{i+1} - p_i$ placed at the midpoint of $[x_i, x_{i+1}]$ as in Siev's worked example, the estimator is

$$\hat\mu_{SK} = \sum_{i=1}^{k-1} (p_{i+1} - p_i)\, \frac{x_i + x_{i+1}}{2}.$$

If the tolerance distribution $F$ is supported in $[x_1, x_k]$ and $p_i = F(x_i)$ for every $i$, then

$$\Bigl|\hat\mu_{SK} - \int x\, dF(x)\Bigr| \le \frac12\max_i\,(x_{i+1} - x_i),$$

since the mass $F(x_{i+1}) - F(x_i)$ of each interval is moved to its midpoint, by at most half its length. The unbiasedness of the estimator for the mean of the interpolated tolerance distribution and its exact variance under binomial sampling are [stated separately](../../../Biology/not-yet-classified/spearman-karber/expect-variance.md).

## Expansion

1. The tolerance model and the Spearman–Kärber estimator with the midpoint convention.
2. The discretization bound, by comparing $\int x\,dF$ with the midpoints interval by interval.
3. The extension of the dose range when the observed proportions do not reach $0$ and $1$, as a separate statement.

## Sources

- D. Siev, Nonparametric estimation of median effective dose, Statistics Section work instruction STATWI0001.02, Center for Veterinary Biologics, United States Department of Agriculture, 2018, Sections 2 and 3.1. <https://direct.aphis.usda.gov/sites/default/files/STATWI0001_4.pdf>
- Original result: C. Spearman, The method of 'right and wrong cases' ('constant stimuli') without Gauss's formulae, Br. J. Psychol. 2 (1908), 227–242. <https://doi.org/10.1111/j.2044-8295.1908.tb00176.x> The estimator follows Siev, Section 3.1.
- Original result: G. Kärber, Beitrag zur kollektiven Behandlung pharmakologischer Reihenversuche, Arch. Exp. Pathol. Pharmakol. 162 (1931), 480–483. <https://doi.org/10.1007/bf01863914> The estimator follows Siev, Section 3.1.
