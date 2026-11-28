# Score, Wald and likelihood-ratio tests

- [Pearson's chi-square goodness-of-fit test](pearson-s-chi-square-goodness-of-fit-test/README.md)
- [Two-sample t and variance-ratio F tests](two-sample-t-and-variance-ratio-f-tests/README.md)

## Chi-square limits

- [Squared normalized Gaussian is chi-square with one degree of freedom](gaussian-real-map-sq-div.md)
- [Law of the positive part squared of a standard normal variable](gaussian-real-map-max-zero-sq.md)
- [Asymptotic law of the Pearson chi-square test of independence](pearson-chi-square-test-of-independence.md)

## Asymptotic tests

- [Second-order Taylor remainder bound](abs-taylor-two-le.md)
- [Rao's score test, known information](tendsto-in-distribution-score-statistic.md)
- [Rao's score test with an estimated information](tendsto-in-distribution-score-statistic-2.md)
- [Consistency of the observed information](tendsto-in-measure-observed-information.md)
- [Wald's test](tendsto-in-distribution-wald-statistic.md)
- [Wald's test with an estimated information](tendsto-in-distribution-wald-statistic-o.md)
- [Quadratic expansion of the log-likelihood ratio](tendsto-in-measure-two-mul-log-likelihoo.md)
- [Wilks' theorem (simple null)](tendsto-in-distribution-two-mul-log-like.md)
- [Wilks' theorem, supremum form](tendsto-in-distribution-two-mul-i-sup-lo.md)
- [Likelihood ratio on the boundary](tendsto-in-distribution-two-mul-log-like-2.md)
- [Asymptotic normality of the difference of two sample proportions](asymptotic-difference-in-proportions-interval.md)

## Kernel score statistics

- [Variance-component score statistic of a general kernel](kernel-q.md)
- [Mixture-weight matrix of a kernel score statistic](kernel-mixture-matrix.md)
- [The SKAT mixture matrix is the mixture matrix of the SKAT kernel](skat-mixture-matrix-eq-kernel-mixture-ma.md)
- [The mixture matrix of a symmetric kernel is symmetric](is-hermitian-kernel-mixture-matrix.md)
- [A positive semidefinite kernel gives nonnegative mixture weights](eigenvalues-kernel-mixture-matrix-nonneg.md)
- [For invertible Xᵀ V⁻¹ X, covariates drop out of the kernel statistic](kernel-q-add-covariates.md)
- [The kernel score statistic is continuous in the phenotype](continuous-kernel-q.md)
- [Kernel statistics of Gaussian phenotypes with mean X α are χ² mixtures](map-kernel-q-multivariate-gaussian.md)

## The burden test

- [Burden score: the weighted sum of the single-variant scores](burden-score.md)
- [Burden test statistic: the squared burden score](burden-q.md)
- [Burden kernel: the outer product of the collapsed genotype](burden-kernel.md)
- [Quadratic form of the null projection at the collapsed genotype](burden-var.md)
- [The burden score is the score of the collapsed genotype](burden-score-eq.md)
- [The burden statistic is the kernel statistic of the burden kernel](burden-q-eq-kernel-q.md)
- [The burden kernel is positive semidefinite](pos-semidef-burden-kernel.md)
- [For invertible Xᵀ V⁻¹ X the burden score ignores covariate effects](burden-score-add-covariates.md)
- [For positive definite V the null burden variance is nonnegative](burden-var-nonneg.md)
- [Burden score of a Gaussian phenotype with mean X α is centred Gaussian](map-burden-score-multivariate-gaussian.md)
- [The burden score is centred Gaussian under the null model](map-burden-score-null.md)
- [The square of a centred Gaussian of variance v has law v χ²₁](gaussian-real-map-sq.md)
- [The burden statistic is a scaled chi-square under the null model](map-burden-q-null.md)
- [The burden statistic has null mean Cᵀ P C](integral-burden-q-null.md)
- [The burden score ignores the weight of a variant with no carriers](burden-score-update-of-col.md)
- [If G a = 0 the null law of the burden score is the point mass at 0](map-burden-score-null-of-collapse-eq-zer.md)
- [The burden statistic is at most m times SKAT with squared weights](burden-q-le-card-mul-skat-q.md)

## SKAT-O

- [The SKAT-O matrix with unit diagonal and off-diagonal entries ρ](skat-ocorr.md)
- [The SKAT-O kernel of a genotype matrix, variant weights and ρ](skat-okernel.md)
- [SKAT-O statistic, an affine combination of SKAT and burden statistics](skat-oq.md)
- [At ρ = 0 the SKAT-O statistic is SKAT with squared weights](skat-oq-zero.md)
- [At ρ = 1 the SKAT-O statistic is the burden statistic](skat-oq-one.md)
- [The SKAT-O kernel as an affine combination of SKAT and burden kernels](skat-okernel-eq.md)
- [The kernel statistic is linear in the kernel](kernel-q-add-smul.md)
- [The SKAT-O statistic is the kernel statistic of the SKAT-O kernel](skat-oq-eq-kernel-q.md)
- [The SKAT-O kernel is symmetric for every ρ](is-hermitian-skat-okernel.md)
- [For 0 ≤ ρ ≤ 1 the SKAT-O kernel is positive semidefinite](pos-semidef-skat-okernel.md)
- [SKAT-O statistics of Gaussian phenotypes with mean X α are χ² mixtures](map-skat-oq-multivariate-gaussian.md)
- [For 0 ≤ ρ ≤ 1 the SKAT-O mixture weights are nonnegative](eigenvalues-skat-o-nonneg.md)

## SKAT-O p-values and Davies' formula

- [Davies' integral for a kernel statistic converges to its mid-p tail](tendsto-davies-kernel-q.md)
- [SKAT-O p-value at a fixed ρ from the null chi-square mixture](skat-opvalue.md)
- [SKAT-O minimum p-value over a finite grid of ρ](skat-omin-p.md)
- [Each SKAT-O p-value is valid under the null for invertible Xᵀ V⁻¹ X](is-valid-pvalue-skat-opvalue.md)
- [Davies' integral gives the SKAT-O p-value when some weight is nonzero](tendsto-davies-skat-opvalue.md)
- [Bonferroni bound for the SKAT-O minimum p-value under the null](measure-skat-omin-p-le.md)

## Related topics

- [SKAT variance-component test](../../../Biology/statistical-genetics/association-tests/skat-variance-component-test/README.md): the SKAT statistic with the null covariance of a mixed model with relatedness, its weighted chi-square law, and kinship and pedigree relationship matrices.
