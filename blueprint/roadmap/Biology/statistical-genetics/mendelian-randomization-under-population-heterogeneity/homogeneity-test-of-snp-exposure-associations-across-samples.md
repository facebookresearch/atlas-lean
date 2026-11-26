# Homogeneity test of SNP-exposure associations across two GWAS samples

In two-sample summary-data Mendelian randomization with independent genetic instruments $Z_1, \dots, Z_p$, the SNP-exposure associations may be estimated twice: $\widehat\gamma_j^{\mathrm{Tr}}$ from the exposure (treatment) sample and $\widehat\gamma_j^{\mathrm{Ou}}$ from the outcome sample, with standard errors $\sigma_{\gamma j,\mathrm{Tr}}$ and $\sigma_{\gamma j,\mathrm{Ou}}$. The classical two-sample design assumes homogeneity, $\gamma_j^{\mathrm{Tr}} = \gamma_j^{\mathrm{Ou}}$ for all $j$; when the samples differ in ancestry, demographics or measurement protocols this can fail.

**Proposition.** Assume $\widehat\gamma_j^{\mathrm{Tr}} \sim N(\gamma_j^{\mathrm{Tr}}, \sigma_{\gamma j,\mathrm{Tr}}^2)$ and $\widehat\gamma_j^{\mathrm{Ou}} \sim N(\gamma_j^{\mathrm{Ou}}, \sigma_{\gamma j,\mathrm{Ou}}^2)$, with the $2p$ estimates mutually independent. Let

$$ T = \sum_{j=1}^{p} \frac{\bigl( \widehat\gamma_j^{\mathrm{Ou}} - \widehat\gamma_j^{\mathrm{Tr}} \bigr)^2}{\sigma_{\gamma j,\mathrm{Ou}}^2 + \sigma_{\gamma j,\mathrm{Tr}}^2}. $$

Under $H_0 : \gamma_j^{\mathrm{Tr}} = \gamma_j^{\mathrm{Ou}}$ for all $j$, $T \sim \chi^2(p)$.

Large $T$ is evidence of population-specific SNP-exposure associations, in which case $\Gamma_j^{\mathrm{Ou}} = \beta_0 \gamma_j^{\mathrm{Ou}} \neq \beta_0 \gamma_j^{\mathrm{Tr}}$ and the classical estimators built from $(\widehat\gamma_j^{\mathrm{Tr}}, \widehat\Gamma_j^{\mathrm{Ou}})$ are inconsistent for the causal effect $\beta_0$.

## Expansion

Under $H_0$ each $T_j = (\widehat\gamma_j^{\mathrm{Ou}} - \widehat\gamma_j^{\mathrm{Tr}}) / \sqrt{\sigma_{\gamma j,\mathrm{Ou}}^2 + \sigma_{\gamma j,\mathrm{Tr}}^2}$ is a difference of independent normals with equal means, hence standard normal, and the $T_j$ are independent across $j$; the sum of their squares is $\chi^2(p)$. The test needs no parametric model for how $\gamma^{\mathrm{Ou}}$ and $\gamma^{\mathrm{Tr}}$ differ. Independence across instruments is the usual approximation after LD clumping, and independence between the two samples holds when they share no individuals.

## Sources

- Dingke Tang, Xuming He, Shu Yang, "A Robust Framework for Two-Sample Mendelian Randomization under Population Heterogeneity", arXiv (2026). Section 2.3, Proposition 1. <https://doi.org/10.48550/arXiv.2604.21757>
