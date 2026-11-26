# Attenuation of correlation under a bivariate liability threshold model

Let $(L_1, L_2)$ be standard bivariate normal with correlation $r_\ell \in [-1, 1]$, and let two diseases be observed as the indicators

$$Y_i = \mathbb{1}\{ L_i > z_i \}, \qquad i = 1, 2,$$

with thresholds $z_1, z_2 \in \mathbb{R}$ fixed by the prevalences. Write $r_p = \operatorname{corr}(Y_1, Y_2)$ for the correlation of the observed case–control phenotypes.

**Attenuation.** $|r_p| \le |r_\ell|$. Equality holds in exactly three cases: $r_\ell = 0$, for any two thresholds, since independent liabilities give independent indicators and $r_p = 0$; $r_\ell = 1$ with $z_1 = z_2$, where $Y_1 = Y_2$; and $r_\ell = -1$ with $z_2 = -z_1$, where $Y_2 = 1 - Y_1$ almost surely. For $0 < |r_\ell| < 1$ the inequality is strict. In particular two diseases with identical liabilities, $r_\ell = 1$, but different thresholds $z_1 \ne z_2$ satisfy $r_p < 1$: dichotomizing at different points destroys correlation even when the underlying traits coincide.

**Recovery.** For fixed $(z_1, z_2)$ the map $r_\ell \mapsto r_p(r_\ell)$ is continuous and strictly increasing on $[-1, 1]$, so it is a bijection onto the attainable range $[r_p(-1), r_p(1)]$ of observed correlations. Given an observed $r_p$ in that range and the prevalences, $r_\ell$ is the unique solution of $r_p(r_\ell) = r_p$, computable by a binary search with $r_p(\cdot)$ evaluated by Monte Carlo or from the bivariate normal orthant probability. A confidence interval for $r_p$, intersected with the attainable range, maps to one for $r_\ell$ under the same inverse map, since the map is monotone.

## Expansion

Both statements follow from the Mehler expansion of the bivariate normal density: for jointly standard normal $(L_1, L_2)$ with correlation $\rho$ and square-integrable $f, g$ with Hermite coefficients $(f_k), (g_k)$,

$$\operatorname{cov}\big(f(L_1), g(L_2)\big) = \sum_{k \ge 1} \rho^{k} \, k! \, f_k g_k .$$

Taking $f = \mathbb{1}\{\cdot > z_1\}$ and $g = \mathbb{1}\{\cdot > z_2\}$ and dividing by the standard deviations writes $r_p = \sum_{k \ge 1} \rho^k a_k b_k$ with $\rho = r_\ell$, where $a_k = \sqrt{k!}\, f_k / \operatorname{sd}(Y_1)$ and $b_k = \sqrt{k!}\, g_k / \operatorname{sd}(Y_2)$ satisfy $\sum_k a_k^2 = \sum_k b_k^2 = 1$. Then $|r_p| \le \sum_k |\rho|^k |a_k b_k| \le |\rho| \sum_k |a_k b_k| \le |\rho|$, the last step by the Cauchy–Schwarz inequality. For $0 < |\rho| < 1$ equality would need $a_k b_k = 0$ for every $k \ge 2$ and $\sum_k |a_k b_k| = 1$, hence $|a_1| = |b_1| = 1$ and $a_k = 0$ for $k \ge 2$, which would make $Y_1$ an affine function of $L_1$; a threshold indicator is not, so the inequality is strict. The three equality cases are the direct computations above.

Monotonicity comes from the orthant probability. Since $r_p = \big(\Pr(L_1 > z_1, L_2 > z_2) - p_1 p_2\big) / \sqrt{p_1(1-p_1) p_2(1-p_2)}$ with $p_i = \Pr(L_i > z_i)$ fixed, $r_p$ is an increasing affine function of the orthant probability, and Plackett's identity gives

$$\frac{\partial}{\partial \rho} \Pr(L_1 > z_1, L_2 > z_2) = \varphi_2(z_1, z_2; \rho) > 0, \qquad -1 < \rho < 1,$$

where $\varphi_2(\cdot, \cdot; \rho)$ is the bivariate standard normal density with correlation $\rho$. A positive derivative throughout the open interval, with continuity at the endpoints, makes the map strictly increasing on $[-1, 1]$.

The practical consequence is that observed-scale correlations of case–control phenotypes are not comparable across diseases of different prevalence, whereas genetic correlations estimated by a bivariate variance-component model on observed case–control phenotypes do carry over to liabilities without transformation; it is the total (phenotypic) correlation, not the genetic one, that needs the inversion above before genetic and total correlations may be compared on the same scale.

## Sources

- P.-R. Loh, G. Bhatia, A. Gusev et al., "Contrasting genetic architectures of schizophrenia and other complex diseases using fast variance-components analysis", Nature Genetics 47 (2015), 1385–1392, Online Methods ("Estimating genetic and total correlations of disease liabilities") and Fig. 5, <https://doi.org/10.1038/ng.3431>, PMCID PMC4666835.
- S. H. Lee, N. R. Wray, M. E. Goddard and P. M. Visscher, "Estimating missing heritability for disease from genome-wide association studies", American Journal of Human Genetics 88 (2011), 294–305 (liability threshold model for case-control data), <https://doi.org/10.1016/j.ajhg.2011.02.002>.
