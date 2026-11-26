# MR-Wald estimator for two-sample Mendelian randomization under population heterogeneity

**Setting.** Instruments $Z_1, \dots, Z_p$ (independent after LD clumping) affect an exposure $X$ and an outcome $Y$. Three sets of GWAS summary statistics are available: SNP-exposure associations $\widehat\gamma_j^{\mathrm{Tr}}$ from the exposure sample, and SNP-exposure and SNP-outcome associations $\widehat\gamma_j^{\mathrm{Ou}}, \widehat\Gamma_j^{\mathrm{Ou}}$ from the outcome sample, unbiased for $\gamma_j^{\mathrm{Tr}}, \gamma_j^{\mathrm{Ou}}, \Gamma_j^{\mathrm{Ou}}$ with known variances $\sigma_{\gamma j,\mathrm{Tr}}^2, \sigma_{\gamma j,\mathrm{Ou}}^2, \sigma_{\Gamma j,\mathrm{Ou}}^2$. The causal model holds in the outcome sample, $\Gamma_j^{\mathrm{Ou}} = \beta_0 \gamma_j^{\mathrm{Ou}} + \alpha_j$, but $\gamma_j^{\mathrm{Tr}}$ may differ from $\gamma_j^{\mathrm{Ou}}$ in an arbitrary way. The exposure-sample estimates are independent of both outcome-sample estimates, which may be dependent on each other.

**Estimator.** With $W^{(1)} = \operatorname{diag}(\sigma_{\gamma j,\mathrm{Ou}}^{-2})$ and $W^{(2)} = \operatorname{diag}(\sigma_{\Gamma j,\mathrm{Ou}}^{-2})$, regress both outcome-sample vectors on the exposure-sample vector by inverse-variance weighting and take the ratio:

$$ \widehat\beta^{\mathrm{MR\text{-}Wald}} = \frac{\widehat{b\beta}}{\widehat b} = \frac{\{(\widehat{\boldsymbol\gamma}^{\mathrm{Tr}})^\top W^{(2)} \widehat{\boldsymbol\gamma}^{\mathrm{Tr}}\}^{-1} (\widehat{\boldsymbol\gamma}^{\mathrm{Tr}})^\top W^{(2)} \widehat{\boldsymbol\Gamma}^{\mathrm{Ou}}}{\{(\widehat{\boldsymbol\gamma}^{\mathrm{Tr}})^\top W^{(1)} \widehat{\boldsymbol\gamma}^{\mathrm{Tr}}\}^{-1} (\widehat{\boldsymbol\gamma}^{\mathrm{Tr}})^\top W^{(1)} \widehat{\boldsymbol\gamma}^{\mathrm{Ou}}}. $$

This is a Wald ratio in which $\widehat\gamma^{\mathrm{Tr}}$ plays the instrument, $\widehat\gamma^{\mathrm{Ou}}$ the exposure and $\widehat\Gamma^{\mathrm{Ou}}$ the outcome.

**Theorem 1.** Assume no pleiotropy ($\alpha_j = 0$), and:

- (B1) with $U_j = (\widehat\Gamma_j^{\mathrm{Ou}} - \Gamma_j^{\mathrm{Ou}}) - \beta_0 (\widehat\gamma_j^{\mathrm{Ou}} - \gamma_j^{\mathrm{Ou}})$ and $\sigma_{Uj}^2 = \operatorname{Var}(U_j)$, the ratios $\sigma_{\gamma j,\mathrm{Ou}}^2 / \sigma_{Uj}^2$ and $\sigma_{\gamma j,\mathrm{Ou}}^2 / \sigma_{\gamma j,\mathrm{Tr}}^2$ lie in a fixed interval $[C_1, C_2] \subset (0,\infty)$, and $\sigma_{\Gamma j,\mathrm{Ou}}^2 = k\, \sigma_{\gamma j,\mathrm{Ou}}^2$ for a constant $k$;
- (B2) with $\kappa_j^{\mathrm{Tr}} = (\gamma_j^{\mathrm{Tr}} / \sigma_{\gamma j,\mathrm{Tr}})^2$, $\kappa_j^{\mathrm{Ou}} = (\gamma_j^{\mathrm{Ou}} / \sigma_{\gamma j,\mathrm{Tr}})^2$, $\kappa_j^{Co} = \sqrt{\kappa_j^{\mathrm{Tr}} \kappa_j^{\mathrm{Ou}}}$ and $\kappa^{\cdot}$ their averages over $j$, $(\kappa^{\mathrm{Tr}})^2 p \to \infty$, $(\kappa^{\mathrm{Ou}})^2 p \to \infty$ and $\sqrt{\kappa^{\mathrm{Tr}} \kappa^{\mathrm{Ou}}} \lesssim \kappa^{Co}$.

Then $\widehat\beta^{\mathrm{MR\text{-}Wald}} \to \beta_0$ in probability. If in addition (B3) the centered $\widehat\gamma_j^{\mathrm{Tr}}$ and $U_j$ have uniformly bounded scaled fourth moments, then $V_1^{-1}(\widehat\beta^{\mathrm{MR\text{-}Wald}} - \beta_0) \to N(0,1)$ with

$$ V_1^2 = \frac{\sum_{j=1}^{p} \bigl( (\gamma_j^{\mathrm{Tr}})^2 + \sigma_{\gamma j,\mathrm{Tr}}^2 \bigr) \sigma_{Uj}^2\, \sigma_{\gamma j,\mathrm{Ou}}^{-4}}{\Bigl( \sum_{j=1}^{p} \gamma_j^{\mathrm{Tr}} \gamma_j^{\mathrm{Ou}} \sigma_{\gamma j,\mathrm{Ou}}^{-2} \Bigr)^2}. $$

Under homogeneity ($\gamma_j^{\mathrm{Tr}} = \gamma_j^{\mathrm{Ou}}$) and $\sigma_{Uj}^2 \le \sigma_{\Gamma j,\mathrm{Ou}}^2$, it is more efficient than the debiased IVW estimator.

**Proposition 2.** If $(\kappa^{\mathrm{Tr}})^2 p \to \infty$ and $|\gamma_j^{\mathrm{Ou}}| \asymp |\gamma_j^{\mathrm{Tr}}|$ uniformly in $j$, then condition B2 holds.

## Depends on

- [Homogeneity test of SNP-exposure associations across two GWAS samples](homogeneity-test-of-snp-exposure-associations-across-samples.md)

## Expansion

Both $\widehat b$ and $\widehat{b\beta}$ suffer regression dilution because $\widehat\gamma^{\mathrm{Tr}}$ is noisy, but since $W^{(2)} = k^{-1} W^{(1)}$ the two denominators are proportional and cancel, leaving $\sum_j \widehat\gamma_j^{\mathrm{Tr}} \widehat\Gamma_j^{\mathrm{Ou}} \sigma_{\gamma j,\mathrm{Ou}}^{-2} \big/ \sum_j \widehat\gamma_j^{\mathrm{Tr}} \widehat\gamma_j^{\mathrm{Ou}} \sigma_{\gamma j,\mathrm{Ou}}^{-2}$. By independence of the samples, numerator and denominator have means $\sum_j \gamma_j^{\mathrm{Tr}} \Gamma_j^{\mathrm{Ou}} \sigma_{\gamma j,\mathrm{Ou}}^{-2}$ and $\sum_j \gamma_j^{\mathrm{Tr}} \gamma_j^{\mathrm{Ou}} \sigma_{\gamma j,\mathrm{Ou}}^{-2}$, whose ratio is exactly $\beta_0$ without any assumed link between $\gamma^{\mathrm{Tr}}$ and $\gamma^{\mathrm{Ou}}$. Condition B2 makes the relative variances of both sums $O\bigl(1/(\kappa^{\mathrm{Tr}} p) + 1/(\kappa^{\mathrm{Ou}} p) + 1/((\kappa^{Co})^2 p)\bigr) = o(1)$, giving consistency even when the average instrument strength stays bounded; a Lindeberg argument on $\sum_j \widehat\gamma_j^{\mathrm{Tr}} U_j \sigma_{\gamma j,\mathrm{Ou}}^{-2}$ gives the normal limit. Pleiotropy is handled separately: balanced pleiotropy keeps the same estimator consistent, and idiosyncratic pleiotropy is handled by replacing the weighted least squares fits with median (absolute-loss) fits.

## Sources

- Dingke Tang, Xuming He, Shu Yang, "A Robust Framework for Two-Sample Mendelian Randomization under Population Heterogeneity", arXiv (2026). Section 3, Theorem 1, Proposition 2; Section 4 (pleiotropy). <https://doi.org/10.48550/arXiv.2604.21757>
