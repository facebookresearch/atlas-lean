# Spearman–Kärber estimator of the mean tolerance

In a bioassay with binary response, the probability of response at dose $x$ is read as the distribution function $F(x)$ of a latent tolerance distribution, an individual's tolerance being the smallest dose that produces a response. The Spearman–Kärber method estimates the mean of the tolerance distribution nonparametrically: the observed response proportions at the doses tested are taken as an empirical distribution function, differencing gives an empirical probability mass function, and the estimate is the mean $\sum x f(x)$ of that discrete distribution; when the observed proportions do not reach $0$ and $1$, the common practice is to assume no response at the next lower dose and complete response at the next higher dose (Siev, Section 3.1). With doses $x_1 < \dots < x_k$ and proportions $p_1 = 0 \le p_2 \le \dots \le p_k = 1$, and the mass $p_{i+1} - p_i$ placed at the midpoint of $[x_i, x_{i+1}]$ as in Siev's worked example, the estimator is
$$\hat\mu_{SK} = \sum_{i=1}^{k-1} (p_{i+1} - p_i)\, \frac{x_i + x_{i+1}}{2}.$$
If the tolerance distribution is supported in $[x_1, x_k]$ and $p_i = F(x_i)$, then $|\hat\mu_{SK} - \int x\, dF| \le \max_i (x_{i+1} - x_i)/2$, since the mass of each interval is moved by at most half its length; and since $\hat\mu_{SK}$ is linear in $(p_i)$, observed proportions unbiased for $F(x_i)$ give an estimator unbiased for its value at the true proportions.

## Expansion

1. The model: doses, a tolerance distribution and binomial responses, and the interval censoring that discretizes the tolerance distribution.
2. The estimator as the mean of the differenced empirical distribution function, and its equally spaced form $x_{(p=1)} + \tfrac12 d - d \sum p$ by summation by parts.
3. The discretization bound when the support lies in $[x_1, x_k]$.
4. Linearity, unbiasedness for the midpoint mean, and the variance $d^2 \sum p(1 - p)/(n - 1)$ under independent binomial responses with spacing $d$ and $n$ subjects per dose.
5. Monotonization of non-monotone observed proportions (the trimmed and pooled versions), and the Reed–Muench and Dragstedt–Behrens estimators, as separate statements.

## Sources

- D. Siev, Nonparametric estimation of median effective dose, Statistics Section work instruction STATWI0001.02, Center for Veterinary Biologics, United States Department of Agriculture, 2018, Sections 2 and 3.1. <https://direct.aphis.usda.gov/sites/default/files/STATWI0001_4.pdf>
- Original result: C. Spearman, The method of 'right and wrong cases' ('constant stimuli') without Gauss's formulae, Br. J. Psychol. 2 (1908), 227–242. <https://doi.org/10.1111/j.2044-8295.1908.tb00176.x> The estimator follows Siev, Section 3.1.
- Original result: G. Kärber, Beitrag zur kollektiven Behandlung pharmakologischer Reihenversuche, Arch. Exp. Pathol. Pharmakol. 162 (1931), 480–483. <https://doi.org/10.1007/bf01863914> The estimator follows Siev, Section 3.1.
