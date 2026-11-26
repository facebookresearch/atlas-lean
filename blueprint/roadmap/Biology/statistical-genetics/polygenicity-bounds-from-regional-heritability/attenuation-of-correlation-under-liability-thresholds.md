# Attenuation of correlation under a bivariate liability threshold model

Let $(L_1, L_2)$ be standard bivariate normal with correlation $r_\ell \in [-1, 1]$, and let two diseases be observed as the indicators

$$Y_i = \mathbb{1}\{ L_i > z_i \}, \qquad i = 1, 2,$$

with thresholds $z_1, z_2 \in \mathbb{R}$ fixed by the prevalences. Write $r_p = \operatorname{corr}(Y_1, Y_2)$ for the correlation of the observed case–control phenotypes.

**Attenuation.** $|r_p| \le |r_\ell|$, with equality only in the degenerate cases $r_\ell \in \{-1, 0, 1\}$ with matched thresholds. In particular two diseases with identical liabilities, $r_\ell = 1$, but different thresholds $z_1 \ne z_2$ satisfy $r_p < 1$: dichotomizing at different points destroys correlation even when the underlying traits coincide.

**Recovery.** For fixed $(z_1, z_2)$ the map $r_\ell \mapsto r_p(r_\ell)$ is continuous and strictly increasing on $[-1, 1]$, so it is invertible: given an observed $r_p$ and prevalences, $r_\ell$ is the unique solution of $r_p(r_\ell) = r_p$, computable by a binary search with $r_p(\cdot)$ evaluated by Monte Carlo (or from the bivariate normal orthant probability). A confidence interval for $r_\ell$ is the image of one for $r_p$ under the same inverse map, since the map is monotone.

## Expansion

Both statements follow from the Mehler expansion of the bivariate normal density: for jointly standard normal $(L_1, L_2)$ with correlation $\rho$ and square-integrable $f, g$ with Hermite coefficients $(f_k), (g_k)$,

$$\operatorname{cov}\big(f(L_1), g(L_2)\big) = \sum_{k \ge 1} \rho^{k} \, k! \, f_k g_k .$$

Taking $f = \mathbb{1}\{\cdot > z_1\}$ and $g = \mathbb{1}\{\cdot > z_2\}$ and dividing by the standard deviations shows that $r_p$ is a power series in $\rho = r_\ell$ with no constant term, whose coefficients are those of the two threshold functions; since the maximal correlation of a bivariate normal pair equals $|\rho|$, no pair of measurable transformations can exceed it, giving $|r_p| \le |r_\ell|$. Strict monotonicity in $\rho$ holds because the first Hermite coefficients of a threshold indicator, $\varphi(z_i)$, are nonzero, so the linear term dominates near $\rho = 0$ and the orthant probability $\Pr(L_1 > z_1, L_2 > z_2)$ is strictly increasing in $\rho$ for fixed thresholds.

The practical consequence is that observed-scale correlations of case–control phenotypes are not comparable across diseases of different prevalence, whereas genetic correlations estimated by a bivariate variance-component model on observed case–control phenotypes do carry over to liabilities without transformation; it is the total (phenotypic) correlation, not the genetic one, that needs the inversion above before genetic and total correlations may be compared on the same scale.

## Sources

- P.-R. Loh, G. Bhatia, A. Gusev et al., "Contrasting genetic architectures of schizophrenia and other complex diseases using fast variance-components analysis", Nature Genetics 47 (2015), 1385–1392, Online Methods ("Estimating genetic and total correlations of disease liabilities") and Fig. 5, <https://doi.org/10.1038/ng.3431>, PMCID PMC4666835.
- S. H. Lee, N. R. Wray, M. E. Goddard and P. M. Visscher, "Estimating missing heritability for disease from genome-wide association studies", American Journal of Human Genetics 88 (2011), 294–305 (liability threshold model for case-control data), <https://doi.org/10.1016/j.ajhg.2011.02.002>.
