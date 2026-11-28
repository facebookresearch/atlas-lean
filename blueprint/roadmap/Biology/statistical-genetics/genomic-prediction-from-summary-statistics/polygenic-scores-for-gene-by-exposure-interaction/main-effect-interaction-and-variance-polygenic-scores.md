# Main-effect, interaction and variance polygenic scores

For individual $i$ with genotype vector $G_i$, exposure $E_i$, outcome $Y_i$ and covariates $C_i$, consider three genome-wide regression models fitted variant by variant:

$$\text{(mean)}\quad Y_i = \beta_0 + \beta_G G_i + \beta_C^\top C_i + \epsilon_i,$$

$$\text{(interaction)}\quad Y_i = \beta_0 + \beta_G G_i + \beta_E E_i + \beta_{G\times E} G_i E_i + \beta_C^\top C_i + \epsilon_i,$$

$$\text{(variance)}\quad \text{a scan returning a variance effect } \beta_{Gv} \text{ per variant},$$

and form three polygenic scores by weighting selected variants with $\hat\beta_G$ (mPGS), $\hat\beta_{G\times E}$ (iPGS) or $\hat\beta_{Gv}$ (vPGS). Each score $S$ is then assessed in an independent sample by the **score-by-exposure** model

$$Y_i = \gamma_0 + \gamma_S S_i + \gamma_E E_i + \gamma_{S \times E} S_i E_i + \gamma_C^\top C_i + \epsilon_i,$$

whose coefficient $\gamma_{S\times E}$ is the change in the exposure–outcome slope per unit of the score and is the quantity the three score types are compared on. Validity requires sample splitting (weights estimated in one subset, the selection threshold tuned in a second, $\gamma_{S\times E}$ estimated in a third held-out subset), since choosing the threshold that minimises the interaction $p$-value in the same data that reports it invalidates the test. When the exposure is adjusted for genetic principal components, the interaction model must also include exposure-by-principal-component products, or population structure can induce a spurious $G\times E$ term.

## Depends on

- [Quantile-integrated variance effect of a variant](quantile-integrated-variance-effect-of-a-variant.md): the variance effect $\beta_{Gv}$ of the variance scan
- [Least squares and the normal equations](../../../../ComputerScience/machine-learning/supervised-learning/least-squares-ridge-and-lasso-regression/rss-le-iff-normal.md): the per-variant and score-by-exposure coefficients are least-squares estimates

## Expansion

The mean scan estimates the average effect of a variant, the interaction scan its effect modification by a measured exposure, and the variance scan its effect on trait spread; a variant interacting with an unmeasured exposure correlated with $E$ shows up in the last but not the second. Because the weights come from different estimands, the three scores can rank individuals differently even when built from the same data. Westerman et al. apply this pipeline in the UK Biobank with body mass index as the exposure, replicate in All of Us, and report significant score-by-BMI interactions for 16 of 20 cardiometabolic risk factors.

## Sources

- K. E. Westerman, J. E. Gervis, L. J. O'Connor, M. S. Udler, A. K. Manning, "Polygenic scores capture genetic modification of the adiposity-cardiometabolic risk factor relationship", Cell Genomics (2026), <https://doi.org/10.1016/j.xgen.2025.101075> (PMC12985365), Results and STAR Methods, "Genome-wide scans" and "Polygenic score generation and optimization".
