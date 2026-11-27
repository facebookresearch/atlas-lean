# Quadratic-form set tests from GWAS summary statistics: fastBAT and mBAT

Let $z = (z_1, \dots, z_m)^\top$ be the GWAS $z$-scores of $m$ SNPs in a gene region and $R$ their LD correlation matrix. Under the
null hypothesis that no SNP in the set is associated with the trait, $z \sim N(0, R)$.

**Lemma (quadratic forms of a Gaussian vector).** If $x \sim N(0, \Sigma)$ and $A$ is symmetric, then

$$Q(x) = x^\top A x \overset{d}{=} \sum_{i=1}^m \Lambda_i\, \chi^2_{1,i},$$

where $\Lambda_1 \ge \dots \ge \Lambda_m$ are the eigenvalues of $\Sigma A$ and the $\chi^2_{1,i}$ are independent central chi-squared
variables with one degree of freedom. If $\Sigma$ is invertible and $A = \Sigma^{-1}$, then $Q(x) \sim \chi^2_m$.

**Tests.**
- *fastBAT:* $T_{\mathrm{fastBAT}} = z^\top z \overset{d}{=} \sum_i \lambda_i \chi^2_{1,i}$ under the null, with $\lambda_i$ the eigenvalues of $R$.
- *mBAT:* with the spectral decomposition of the positive part of $R$, $R^- = U D^{-1} U^\top$, $D = \operatorname{diag}(\lambda_1,\dots,\lambda_p)$
  the $p$ positive eigenvalues and $U \in \mathbb{R}^{m\times p}$ orthonormal eigenvectors,

$$T_{\mathrm{mBAT}} = z^\top R^- z = \sum_{i=1}^p \lambda_i^{-1} (U_i^\top z)^2 \sim \chi^2_p \quad \text{under the null.}$$

**Interpretation.** With standardized genotypes $X \in \mathbb{R}^{n\times m}$, true joint effects $\beta$ and unit phenotypic variance,
the variance explained by the set is $V_g = \beta^\top R \beta$, and the marginal estimates satisfy $b = R\beta + e$ with
$\operatorname{Var}(e) = R/n$. Substituting $\beta \approx R^{-1} b$ gives $V_g \approx b^\top R^{-1} b$ and, since $z = \sqrt n\, b$,

$$T_{\mathrm{mBAT}} = n\, b^\top R^{-1} b \approx n V_g,$$

so mBAT tests for nonzero joint variance explained, and is not attenuated by *masking* (marginal effects cancelling because two
causal effects have the same sign while their LD correlation is negative, or opposite signs while it is positive).

## Proof depends on

- [A standard Gaussian quadratic form has a weighted chi-square law](../std-gaussian-map-inner-eq-weighted-chi-s.md)

## Expansion

Write $x = \Sigma^{1/2} g$ with $g \sim N(0, I)$; then $x^\top A x = g^\top \Sigma^{1/2} A \Sigma^{1/2} g$ and diagonalizing the
symmetric matrix $\Sigma^{1/2} A \Sigma^{1/2}$, whose eigenvalues are those of $\Sigma A$, gives the weighted chi-squared sum. For mBAT,
$U_i^\top z \sim N(0, \lambda_i)$ independently across $i$, so $\lambda_i^{-1}(U_i^\top z)^2$ are independent $\chi^2_1$. fastBAT weights
directions by $\lambda_i$, favouring the dominant LD direction; mBAT weights all identifiable directions equally, which is what
recovers signal in low-eigenvalue directions where masked effects live. (Li et al. 2023, Equations 1–4 and the pseudo-inverse
construction.)

## Sources

- A. Li, S. Liu, A. Bakshi et al., "mBAT-combo: A more powerful test to detect gene-trait associations from GWAS data", The American Journal of Human Genetics (2023), <https://doi.org/10.1016/j.ajhg.2022.12.006> (PMC9892780).
