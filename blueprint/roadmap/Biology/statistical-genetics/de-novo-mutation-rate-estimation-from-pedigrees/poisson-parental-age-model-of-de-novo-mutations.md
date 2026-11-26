# Poisson parental-age model of de novo mutations

For a species with haploid autosomal genome size $H$ (in bp) and gestation time $C$, let $Y^s$ be the number of de novo mutations a child inherits on the parental background of sex $s \in \{\mathrm{male}, \mathrm{female}\}$, and $B^s$ the parent's age at the child's birth. The model is

$$Y^s \sim \mathrm{Poisson}\big(\beta^s_0 + \beta^s_1 (B^s - C)\big),$$

with intercept $\beta^s_0$ (mutations at conception age zero) and parental age effect $\beta^s_1$ per year, fitted by maximum likelihood separately for each sex (identity-link Poisson regression). Given typical ages at conception $G^{\mathrm m}$ and $G^{\mathrm f}$, the per-base-pair, per-generation mutation rates are

$$\mu^s(G^s) = \frac{\beta^s_0 + \beta^s_1 G^s}{2H}, \qquad \mu_g = \mu^{\mathrm m}(G^{\mathrm m}) + \mu^{\mathrm f}(G^{\mathrm f}),$$

and the male-to-female mutation ratio at those ages is

$$\alpha = \frac{\beta^{\mathrm m}_0 + \beta^{\mathrm m}_1 G^{\mathrm m}}{\beta^{\mathrm f}_0 + \beta^{\mathrm f}_1 G^{\mathrm f}}.$$

**Properties.** (i) With $\lambda_i = \beta_0 + \beta_1 (B_i - C) > 0$, the maximum likelihood estimates solve the score equations

$$\sum_i \Big(\frac{Y_i}{\hat\lambda_i} - 1\Big) = 0, \qquad \sum_i (B_i - C)\Big(\frac{Y_i}{\hat\lambda_i} - 1\Big) = 0 .$$

(ii) Testing whether the age effect equals a value $b$ predicted by a cell-division model (for example, the human slope times a ratio of spermatogonial division rates) is a likelihood-ratio test of $\beta^{\mathrm m}_1 = b$, asymptotically $\chi^2_1$ under the null. (iii) $\mu_g$ is linear in the generation times, so a change in life history changes the per-generation rate even with fixed per-year age effects.

## Expansion

The Poisson log-likelihood is $\sum_i (Y_i \log \lambda_i - \lambda_i)$ up to constants; differentiating in $\beta_0$ and $\beta_1$ with $\partial \lambda_i/\partial\beta_0 = 1$ and $\partial\lambda_i/\partial\beta_1 = B_i - C$ gives (i). The child inherits two haploid genomes of $H$ bp each, one per parent, so $(Y^{\mathrm m} + Y^{\mathrm f})/(2H)$ is the per-bp mutation rate per transmitted haploid genome per generation; splitting the numerator by parental sex gives $\mu_g = \mu^{\mathrm m} + \mu^{\mathrm f}$ with the stated $\mu^s$. Wu et al. fit the model to pedigree DNM counts after correcting for false discoveries, false negatives and the accessible genome fraction, and find a baboon paternal age effect inconsistent with the $1.5$-fold increase over humans expected if mutations tracked spermatogonial stem-cell divisions.

## Depends on

- [Transmission-based false discovery rate for de novo mutations](transmission-based-false-discovery-rate-for-de-novo-mutations.md)

## Sources

- F. L. Wu, A. I. Strand, L. A. Cox, C. Ober, J. D. Wall, P. Moorjani and M. Przeworski, "A comparison of humans and baboons suggests germline mutation rates do not track cell divisions", PLoS Biology 18 (2020), e3000838, Methods "Calculating per-generation mutation rates and age effects" and "Testing age effects and intercepts", <https://doi.org/10.1371/journal.pbio.3000838>, PMCID PMC7467331.
