# Plug-in identification of receptor-modulated ligand effects

For individual $i$, let $X_i$ be ligand expression in a sender cell type, $Z_i$ receptor expression in a receiver cell type and $Y_i$ downstream pathway activity in the receiver, with cis-eQTL instruments $G_i$ (ligand) and $H_i$ (receptor), observed covariates $V_i$ and an unobserved confounder $U_i$. The structural model is

$$X_i = \pi_X^\top G_i + \alpha_X^\top V_i + \lambda_XU_i + \varepsilon_{Xi}, \qquad Z_i = \pi_Z^\top H_i + \alpha_Z^\top V_i + \lambda_ZU_i + \varepsilon_{Zi},$$

$$Y_i = \beta_XX_i + \beta_ZZ_i + \beta_{XZ}X_iZ_i + \alpha_Y^\top V_i + \lambda_YU_i + \varepsilon_{Yi},$$

with independent mean-zero errors. The causal effect of ligand on pathway activity is receptor modulated: $\partial Y/\partial X = \beta_X + \beta_{XZ}Z_i$. Define the instrument-based conditional means $X_i^* = \pi_X^\top G_i + \alpha_X^\top V_i$ and $Z_i^* = \pi_Z^\top H_i + \alpha_Z^\top V_i$.

**Proposition 1 (identification).** Assume relevance ($\pi_X \neq 0$, $\pi_Z \neq 0$), exclusion ($G_i,H_i$ do not affect $Y_i$ directly), independence ($U_i \perp (G_i,H_i,V_i)$), and centered confounding $E[U_i] = 0$. Then

$$E[Y_i \mid X_i^*,Z_i^*,V_i] = \mu + \beta_XX_i^* + \beta_ZZ_i^* + \beta_{XZ}X_i^*Z_i^* + \alpha_Y^\top V_i, \qquad \mu = \beta_{XZ}\lambda_X\lambda_ZE[U_i^2],$$

so the plug-in regression of $Y$ on $(X^*,Z^*,X^*Z^*,V)$ with an intercept identifies $(\beta_X,\beta_Z,\beta_{XZ})$.

## Depends on

- [Ratio estimate of a single SNP](ratio-estimate.md)

## Expansion

Write $X = X^* + \eta_X$ and $Z = Z^* + \eta_Z$ with $\eta_X = \lambda_XU + \varepsilon_X$. Expanding $XZ = X^*Z^* + X^*\eta_Z + Z^*\eta_X + \eta_X\eta_Z$ and conditioning on $(G,H,V)$, the terms linear in $\eta$ vanish because $\eta$ has mean zero independently of the instruments, while $E[\eta_X\eta_Z] = \lambda_X\lambda_ZE[U^2]$ is constant. The interaction therefore adds only an intercept, which is why the working model must keep one even with centered data; it vanishes when $\beta_{XZ} = 0$ or the confounder does not reach both exposures. Without the centering $E[U] = 0$, terms such as $\beta_{XZ}\lambda_ZE[U]X^*$ would bias the main effects. With a single exposure and no interaction this reduces to standard two-stage least squares, whose single-instrument form is the ratio estimate.

## Sources

- Bitan Sarkar and Yang Ni, *MR-CCC: Bayesian Mendelian Randomization for Causal Cell–Cell Communication*, arXiv:2604.23917 (2026). <https://doi.org/10.48550/arXiv.2604.23917> Methods, "Structural Model and Identification" (Proposition 1 and the following remark).
