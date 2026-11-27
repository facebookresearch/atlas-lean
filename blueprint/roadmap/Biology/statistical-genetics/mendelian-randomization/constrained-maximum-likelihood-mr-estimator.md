# Constrained maximum-likelihood Mendelian randomization (cML-MR)

Let $g_1, \dots, g_m$ be independent SNPs used as instruments for an exposure $X$ and outcome $Y$, with causal effect $\theta$. Their total effects satisfy

$$\beta_{Yi} = \theta\, \beta_{Xi} + r_i, \qquad i = 1, \dots, m,$$

where $r_i$ is the direct (pleiotropic) effect of $g_i$ on $Y$, whether uncorrelated ($\alpha_i$) or correlated through a confounder ($\beta_{YU}\varphi_i$); instrument $i$ is valid iff $r_i = 0$. From two independent GWAS one observes $\hat\beta_{Xi} \sim N(\beta_{Xi}, \hat\sigma_{Xi}^2)$ and $\hat\beta_{Yi} \sim N(\beta_{Yi}, \hat\sigma_{Yi}^2)$, giving the log-likelihood

$$L(\theta, \{b_{Xi}, r_i\}) = -\frac12 \sum_{i=1}^m \Bigl( \frac{(\hat\beta_{Xi} - b_{Xi})^2}{\hat\sigma_{Xi}^2} + \frac{(\hat\beta_{Yi} - \theta b_{Xi} - r_i)^2}{\hat\sigma_{Yi}^2} \Bigr).$$

For an integer $K$ (the assumed number of invalid instruments), the **constrained MLE** $(\hat\theta(K), \hat b_{Xi}(K), \hat r_i(K))$ maximizes $L$ subject to $\sum_{i=1}^m \mathbf 1(r_i \ne 0) = K$; let $\hat B_K = \{ i : \hat r_i(K) \ne 0 \}$. The number $K$ is chosen from a candidate set $\mathcal K$ by

$$\mathrm{BIC}(K) = -2 L\bigl(\hat\theta(K), \{\hat b_{Xi}(K), \hat r_i(K)\}\bigr) + K \log n, \qquad \hat K = \arg\min_{K \in \mathcal K} \mathrm{BIC}(K),$$

with $n = \min(n_1, n_2)$ the smaller GWAS sample size.

**Theorem (selection consistency).** Let $B_0 = \{ i : r_i \ne 0\}$, $K_0 = |B_0|$. Assume (plurality validity) that for every $B \ne B_0$ with $|B| = K_0$ the ratios $\{ r_i / \beta_{Xi} : i \notin B \}$ are not all equal, and that there are constants with $l_X/n_1 \le \hat\sigma_{Xi}^2 \le u_X/n_1$, $l_Y/n_2 \le \hat\sigma_{Yi}^2 \le u_Y/n_2$ and $l_n n_2 \le n_1 \le u_n n_2$. If $K_0 \in \mathcal K$, then $P(\hat K = K_0) \to 1$ and $P(\hat B_{\hat K} = B_0) \to 1$ as $n_1, n_2 \to \infty$ with $m$ fixed. After correct selection, $\hat\theta(\hat K)$ coincides with the profile-likelihood estimate on the valid instruments and is consistent and asymptotically normal.

## Depends on

- [Ratio estimate of a single SNP](ratio-estimate.md)
- [Inverse-variance-weighted estimator](ivw.md)
- [Profile-likelihood Mendelian randomization estimator under many weak instruments](mr-profile-likelihood-estimator-under-weak-instruments.md)

## Expansion

Setting $r_i$ free for $i \in B$ lets those instruments fit $\hat\beta_{Yi}$ exactly, so they drop out of the information about $\theta$; the constraint is an $\ell_0$ budget on pleiotropy. The likelihood penalty for wrongly treating an invalid instrument as valid grows like $n\, r_i^2$, while wrongly freeing a valid instrument gains only $O_p(1)$ in $-2L$ but costs $\log n$; plurality validity rules out an alternative set of $K_0$ instruments whose remaining ratios agree on a common $\theta$. Together these give BIC consistency.

## Sources

- H. Xue, X. Shen and W. Pan, *Constrained maximum likelihood-based Mendelian randomization robust to both correlated and uncorrelated pleiotropic effects*, Am. J. Hum. Genet. 108 (2021), 1251–1269, <https://doi.org/10.1016/j.ajhg.2021.05.014>, PMCID PMC8322939, Material and methods: Equations 1–4, Assumptions 1–2 and Theorem 1.
