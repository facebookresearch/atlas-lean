# Single-component moment estimator of heritability and its null law

Let $y \in \mathbb R^n$ be a phenotype standardised to unit variance and let $R$ be a symmetric positive semidefinite $n \times n$ genetic relationship matrix normalised so that $\operatorname{tr} R = n$ (for example a local relationship matrix built from mutations of an ancestral recombination graph in a gene region). Under the single-component model $\mathbb E[y] = 0$, $\operatorname{Cov}(y) = \sigma_g^2 R + (1 - \sigma_g^2) I_n$, the method-of-moments (randomized Haseman–Elston) estimator

$$\tilde\sigma_g^2 = \frac{y^\top (R - I_n)\,y}{\operatorname{tr}(R^2) - n}$$

is unbiased for $\sigma_g^2$ whenever $\operatorname{tr}(R^2) > n$, that is, whenever $R \ne I_n$. Under the null hypothesis $H_0 : \sigma_g^2 = 0$ with Gaussian $y \sim \mathcal N(0, I_n)$, the random part $T = y^\top R\,y$ of its numerator has the weighted chi-square law

$$T \overset{d}{=} \sum_{i=1}^n \lambda_i\, \chi^2_{1,i},$$

where $\lambda_1 \ge \dots \ge \lambda_n \ge 0$ are the eigenvalues of $R$ and the $\chi^2_{1,i}$ are independent chi-square variables with one degree of freedom. $T$ is the same quadratic form as the variance-component score statistic of SKAT, with variant weights given by the construction of $R$.

## Depends on

- [GREML covariance matrix](../greml-cov.md): the single-component covariance $\sigma_g^2 R + (1-\sigma_g^2) I_n$
- [A standard Gaussian quadratic form has a weighted chi-square law](../../association-tests/skat-variance-component-test/std-gaussian-map-inner-eq-weighted-chi-s.md): the null law of $T$
- [SKAT variance-component score statistic](../../association-tests/skat-variance-component-test/skat-q.md): the identification of $T$ with the SKAT statistic

## Proof depends on

- [Expected output quadratic form equals a trace](../../../../InformationTheory/not-yet-classified/part-01/linear-gaussian-all-law-converse/integral-output-quadratic-eq-trace.md): $\mathbb E[y^\top A y] = \operatorname{tr}(A\operatorname{Cov}(y))$ for unbiasedness

## Expansion

For any symmetric $A$, $\mathbb E[y^\top A y] = \operatorname{tr}(A\,\operatorname{Cov}(y))$. With $A = R - I$ and $\operatorname{tr} R = n$, $\operatorname{tr}((R - I)R) = \operatorname{tr}(R^2) - n$ and $\operatorname{tr}(R - I) = 0$, so $\mathbb E[y^\top(R - I)y] = \sigma_g^2(\operatorname{tr}(R^2) - n)$. Since the eigenvalues of $R$ have mean $1$, $\operatorname{tr}(R^2) - n = \sum_i (\lambda_i - 1)^2 \ge 0$ with equality only for $R = I$. For the null law, rotate $y$ by the orthogonal eigenvector matrix of $R$; the standard Gaussian is rotation invariant. The number of nonzero $\lambda_i$ is at most the number of variants in the region, usually too small for a normal approximation, so Zhu et al. (ARG-RHE) estimate the top eigenvalues by randomized SVD with genealogy-based matrix products, approximate the tail by $\sum_{i \le L}\lambda_i \chi^2_{1,i} + a\chi^2_d$ with a moment-matched remainder, and refine small $p$-values by a saddle-point approximation; $\operatorname{tr}(R^2)$ is obtained by Hutchinson's estimator. Applied to an ARG of 337,464 UK Biobank individuals and 52 blood traits, the test recovered gene-level associations missed by imputation-based tests.

## Sources

- J. Zhu et al., "Leveraging ancestral recombination graphs for scalable mixed-model analysis of complex traits", Cell Genomics (2026), <https://doi.org/10.1016/j.xgen.2025.101072> (PMC12903391), STAR Methods, "Efficient ARG-based variance component association testing", Equations 2–4.
