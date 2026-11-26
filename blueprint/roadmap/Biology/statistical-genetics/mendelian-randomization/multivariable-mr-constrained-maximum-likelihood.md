# Multivariable constrained maximum likelihood (MVMR-cML) and its BIC consistency

Let $\hat\beta_i = (\hat\beta_{X_1 i}, \dots, \hat\beta_{X_L i}, \hat\beta_{Y i})^\top$, $i = 1, \dots, m$, be GWAS
summary statistics of $m$ independent instruments, modelled as mutually independent with

$$\hat\beta_i \sim N\!\Bigl(b_i,\ \Sigma_i\Bigr), \qquad b_i = \Bigl(b_{X_1 i}, \dots, b_{X_L i},\ \textstyle\sum_{l=1}^L \theta_l b_{X_l i} + r_i\Bigr)^\top,$$

with known covariance matrices $\Sigma_i$ (diagonal when the $L+1$ GWAS use non-overlapping samples). The log-likelihood is

$$\ell(\theta, \{b_{X i}\}, \{r_i\}) = -\frac12 \sum_{i=1}^m (\hat\beta_i - b_i)^\top \Sigma_i^{-1} (\hat\beta_i - b_i).$$

For a number $K$ of invalid instruments, the **constrained maximum likelihood estimator** is

$$(\hat\theta^{(K)}, \{\hat b_{X i}^{(K)}\}, \{\hat r_i^{(K)}\}) = \arg\max\ \ell \quad \text{subject to} \quad \sum_{i=1}^m \mathbf 1(r_i \ne 0) = K,$$

and $K$ is chosen from a candidate set $\mathcal K$ by

$$\mathrm{BIC}(K) = -2\,\ell\bigl(\hat\theta^{(K)}, \{\hat b_{X i}^{(K)}\}, \{\hat r_i^{(K)}\}\bigr) + \log(N)\, K,$$

where $N = \min(N_{X_1}, \dots, N_{X_L}, N_Y)$ is the smallest GWAS sample size. Set $\hat K = \arg\min_{K} \mathrm{BIC}(K)$,
$\hat V = \{ i : \hat r_i^{(\hat K)} = 0 \}$ and $\hat\theta = \hat\theta^{(\hat K)}$.

**Theorem.** Assume the [multivariable plurality condition](multivariable-mr-plurality-identifiability.md), the
Gaussian model above with known $\Sigma_i$, and constants $0 < c_1 \le c_2$ with
$c_1/N \le \sigma_{X_l i}^2,\ \sigma_{Y i}^2 \le c_2/N$ for all $l, i$. Then as $N \to \infty$,
$P(\hat K = m - m_0) \to 1$ and $P(\hat V = V^*) \to 1$, and $\hat\theta$ is consistent for $\theta^*$ with

$$V^{1/2} (\hat\theta - \theta^*) \xrightarrow{d} N(0, I_L),$$

where $V$ is the expected Fisher information of the profile log-likelihood of $\theta$ over the valid instruments.

## Depends on

- [Identifiability of multivariable Mendelian randomization under a plurality rule](multivariable-mr-plurality-identifiability.md)
- [Inverse-variance-weighted estimator](ivw.md)

## Expansion

For fixed $K$ the maximization alternates three closed-form steps: compute the unconstrained $\hat r_i$ for each
instrument and keep nonzero only the $K$ instruments whose likelihood gain from freeing $r_i$ is largest; update
each $b_{X i}$; update $\theta$. At convergence the instruments flagged invalid do not contribute to $\hat\theta$, so
$\hat\theta$ is the profile maximum likelihood estimator on the selected valid set. Under the plurality rule an
invalid instrument left constrained costs a likelihood penalty of order $N$, while freeing a valid one gains
$O_p(1)$, against a BIC penalty of $\log N$; this gives selection consistency, after which standard profile
likelihood asymptotics apply. (Lin, Xue and Pan 2023, Equations 5–7, Assumptions 2–3 and Theorem 2.)

## Sources

- Zhaotong Lin, Haoran Xue, Wei Pan, "Robust multivariable Mendelian randomization based on constrained maximum likelihood", The American Journal of Human Genetics (2023), <https://doi.org/10.1016/j.ajhg.2023.02.014> (PMC10119150).
