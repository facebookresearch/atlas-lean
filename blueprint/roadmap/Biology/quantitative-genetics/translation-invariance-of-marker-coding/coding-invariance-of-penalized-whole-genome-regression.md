# Coding invariance of penalized whole-genome regression with interactions

**Setting.** Fit a complete polynomial model of total degree $D$ in marker values to phenotypes $y\in\mathbb R^n$ by minimizing

$$\sum_{i=1}^n\bigl(y_i-f(M_{i,\bullet})\bigr)^2+\mathrm{pen}(f),$$

with penalty factors held fixed, and compare the fit on the coding $M$ with the fit on a translated coding $\tilde M=M-\mathbf 1_nP^{t}$.

**Corollary 1 (OLS).** For a complete polynomial model of total degree $D$, the ordinary least-squares estimates of the coefficients of highest total degree and the fitted predictions $\hat y$ are invariant under translations of the marker coding.

**Corollary 2 (top-degree penalties).** For a complete polynomial model of total degree $D$ and any penalty that depends only on the coefficients of monomials of highest total degree, the estimates of those coefficients and the predictions $\hat y$ are invariant under translations of the marker coding.

**Corollary 3 (RRBLUP).** Ridge-regression BLUP of the additive model $y_i=\mu+\sum_j\beta_jM_{i,j}+\epsilon_i$, with $\mu$ fixed and penalty $\lambda\sum_j\beta_j^2$ for a fixed $\lambda=\sigma_\epsilon^2/\sigma_\beta^2$, gives predictions invariant under translations of the marker coding.

**Corollary 4 (additive LASSO).** An additive LASSO with an $\ell_1$ penalty on the marker effects and an unpenalized intercept is invariant under translations of the marker coding.

**Non-invariance.** Invariance fails as soon as a lower-degree coefficient is penalized. Extended RRBLUP (eRRBLUP) of the pairwise epistasis model, with $\beta_k\sim N(0,\sigma_\beta^2)$, $h_{k,l}\sim N(0,\sigma_h^2)$ and penalty factors $\lambda_1=\sigma_\epsilon^2/\sigma_\beta^2>0$, $\lambda_2=\sigma_\epsilon^2/\sigma_h^2$, gives interaction estimates and predictions that depend on the coding; so does pure ridge regression of the additive model with a penalty on the intercept. Setting $\lambda_1=0$ (additive effects fixed, only interactions penalized) restores invariance by Corollary 2.

## Expansion

By the top-degree invariance proposition, every candidate $f$ on the original coding corresponds to a $\tilde f$ on the translated coding with the same residual sum of squares and the same top-degree coefficients. If the objective sees only the residual sum of squares and the top-degree coefficients, then $f$ and $\tilde f$ have the same objective value, so the minimizers correspond and share predictions and top-degree estimates. Corollaries 3 and 4 are the degree-1 case. A penalty on additive effects in a degree-2 model is a penalty on lower-degree coefficients, which change under the translation, so the objective is no longer matched. On a wheat data set with variance components fixed from the centred coding, some interaction effects ranked among the 4% largest in absolute value under one coding and among the 4% smallest under another, and the discrepancy grew with the number of modelled interactions.

## Depends on

- [Top-degree coefficients are invariant under a translation of the marker coding](top-degree-coefficients-invariant-under-marker-recoding.md)
- [Closed form of ridge regression](../../../ComputerScience/machine-learning/supervised-learning/least-squares-ridge-and-lasso-regression/ridge-le-ridge-estimate.md)
- [Lasso objective](../../../ComputerScience/machine-learning/supervised-learning/least-squares-ridge-and-lasso-regression/lasso.md)

## Sources

- J. W. R. Martini, F. Rosales, N.-T. Ha, J. Heise, V. Wimmer, T. Kneib, "Lost in Translation: On the Problem of Data Coding in Penalized Whole Genome Regression with Interactions", *G3: Genes, Genomes, Genetics* (2019), Corollaries 1–4, Examples 1 and 4, Equations (4)–(6), the wheat data analysis and Discussion, and Appendix proofs of Corollaries 1–4, <https://doi.org/10.1534/g3.118.200961>, PMCID PMC6469405.
