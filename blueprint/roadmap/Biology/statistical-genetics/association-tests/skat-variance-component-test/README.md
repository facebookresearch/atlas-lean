# SKAT variance-component test

The SKAT variance-component score test for rare variants (Wu et al. 2011), with the null covariance
of a mixed model with relatedness used for family samples (Chen et al. 2013): the statistic, its
weighted chi-square law for Gaussian phenotypes with mean in the span of the covariates, its mean
for such phenotypes under the null hypothesis and along the variance-component alternative, and
boundary cases: the variance component at the boundary `τ = 0`, rare alleles, variants without
carriers and singular relationship matrices.

## Statistic and its law

- [A standard Gaussian quadratic form has a weighted chi-square law](std-gaussian-map-inner-eq-weighted-chi-s.md)
- [The weighted chi-square law has mean equal to the sum of its weights](integral-weighted-chi-sq.md)
- [A weighted chi-square law with nonnegative weights has no mass below 0](weighted-chi-sq-iio-eq-zero.md)
- [Null phenotypic covariance with relatedness](null-cov.md)
- [Weighted linear SKAT kernel](skat-kernel.md)
- [Phenotypic covariance under the variance-component alternative](alt-cov.md)
- [Null-model GLS residual](gls-residual.md)
- [SKAT variance-component score statistic](skat-q.md)
- [Null projection matrix of the SKAT test](proj-p.md)
- [Single-variant score statistics](variant-score.md)
- [Mixture matrix of the SKAT statistic](skat-mixture-matrix.md)
- [Scaling the GLS residual by the inverse covariance gives P y](inv-mul-vec-gls-residual.md)
- [The SKAT statistic as a quadratic form in P y](skat-q-eq.md)
- [Quadratic form of the SKAT kernel as a weighted sum of squares](dot-product-skat-kernel-mul-vec.md)
- [SKAT as a weighted sum of squared single-variant scores](skat-q-eq-sum-variant-score.md)
- [The null projection annihilates the covariates](proj-p-mul-self.md)
- [Covariate effects drop out of the SKAT statistic](skat-q-add-covariates.md)
- [The SKAT kernel is symmetric](is-hermitian-skat-kernel.md)
- [With nonnegative weights the SKAT kernel is positive semidefinite](pos-semidef-skat-kernel.md)
- [The SKAT mixture matrix is symmetric](is-hermitian-skat-mixture-matrix.md)
- [With nonnegative variant weights the mixture weights are nonnegative](eigenvalues-skat-mixture-matrix-nonneg.md)
- [The SKAT statistic is continuous in the phenotype](continuous-skat-q.md)
- [SKAT statistics of Gaussian phenotypes with mean X α are χ² mixtures](map-skat-q-multivariate-gaussian.md)

## Weights and means

- [The trace of the SKAT kernel times a matrix splits over variants](trace-skat-kernel-mul.md)
- [The mixture weights sum to tr(K P V' Pᵀ)](sum-eigenvalues-skat-mixture-matrix.md)
- [Mean of the SKAT statistic for a Gaussian phenotype with mean X α](integral-skat-q-multivariate-gaussian.md)
- [For a positive definite covariance the null projection is symmetric](transpose-proj-p.md)
- [The null projection satisfies P V P = P](proj-p-mul-mul-proj-p.md)
- [The null mean of the SKAT statistic is tr(K P)](integral-skat-q-null.md)

## Boundary case: the variance component at τ = 0

- [With nonnegative weights the SKAT statistic is nonnegative](skat-q-nonneg.md)
- [At τ = 0 the alternative covariance is the null covariance](alt-cov-zero.md)
- [With nonnegative weights tr(K P K Pᵀ) is nonnegative](trace-skat-kernel-mul-proj-p-nonneg.md)
- [Mean of the SKAT statistic along the variance-component alternative](integral-skat-q-alt-cov.md)
- [The mean of the SKAT statistic is smallest at τ = 0](integral-skat-q-null-le-alt-cov.md)
- [Under the null the SKAT statistic is almost surely nonnegative](map-skat-q-null-iio.md)

## Boundary case: rare alleles

- [Default SKAT variant weight from the Beta(1, 25) density](beta-weight.md)
- [The default weight at frequency zero is 625](beta-weight-zero.md)
- [The default weight at frequency one is zero](beta-weight-one.md)
- [The default weight is non-increasing on the unit interval](beta-weight-antitone-on.md)
- [On the unit interval the default weight is at most 625](beta-weight-le.md)
- [Diagonal entries of Gᵀ N G are quadratic forms in the columns of G](transpose-mul-mul-apply-self.md)
- [The null mean of the SKAT statistic splits over variants](integral-skat-q-null-eq-sum.md)

## Boundary case: zero minor-allele count

- [A variant with no carriers has score zero](variant-score-eq-zero-of-col.md)
- [Reweighting a carrier-free variant leaves the SKAT statistic unchanged](skat-q-update-of-col.md)
- [With no carriers at any variant the SKAT statistic is zero](skat-q-zero-genotype.md)
- [With no carriers at any variant every mixture weight is zero](eigenvalues-skat-mixture-matrix-zero-gen.md)
- [With no carriers the law of the SKAT statistic is the point mass at 0](map-skat-q-zero-genotype.md)

## Boundary case: singular kinship

- [With residual noise the null covariance is positive definite](pos-def-null-cov.md)
- [Without residual noise a null vector of Φ is a null vector of Σ₀](null-cov-zero-mul-vec.md)
- [Without residual noise a singular Φ gives a singular null covariance](det-null-cov-zero.md)
- [A singular covariance makes the null projection zero](proj-p-of-det-eq-zero.md)
- [A singular null covariance makes the SKAT statistic zero](skat-q-of-det-eq-zero.md)
- [A singular covariance confines the phenotype to a hyperplane](ae-dot-product-sub-eq-zero.md)

## Relation to the BOLT-LMM model

- [The null covariance is the BOLT-LMM marginal covariance](null-cov-eq-v.md)
- [The null projection is the BOLT-LMM residual-forming matrix](proj-p-eq-proj.md)

## The pedigree relationship matrix

- [Twice the kinship matrix of an IBD model is positive semidefinite](pos-semidef-two-kinship.md)
- [Additive relationship matrix of a pedigree](pedigree-relationship.md)
- [A pedigree's additive relationship matrix is positive semidefinite](pos-semidef-pedigree-relationship.md)
- [With residual noise the pedigree null covariance is positive definite](pos-def-null-cov-pedigree-relationship.md)

## Mixed-model, set-based and EHR association tests

- [Mixed-model, set-based and EHR association tests](mixed-model-set-based-and-ehr-association-tests/README.md)

## Related topics

- [Score, Wald and likelihood-ratio tests](../../../../Probability/hypothesis-testing/score-wald-and-likelihood-ratio-tests/README.md): the burden test and SKAT-O as kernel score statistics `(P y)ᵀ K (P y)` with chi-square mixture laws. At a fixed `ρ`, [Davies' formula](../../../../Probability/hypothesis-testing/score-wald-and-likelihood-ratio-tests/tendsto-davies-skat-opvalue.md) computes the [SKAT-O p-value](../../../../Probability/hypothesis-testing/score-wald-and-likelihood-ratio-tests/skat-opvalue.md) `p_ρ(y) = ν_ρ([Q_ρ(y), ∞))` of the mixture law `ν_ρ` when some mixture weight `λⱼ(ρ)` is nonzero. The condition matters: with all variant weights `0`, `Q_ρ = 0` and every `λⱼ(ρ) = 0`, so `p_ρ = 1` while the Davies expression is `1/2`. For a nonempty finite grid of `ρ`, the individual tail calculations do not in general give an exact grid-adjusted p-value for the [minimum of these p-values](../../../../Probability/hypothesis-testing/score-wald-and-likelihood-ratio-tests/skat-omin-p.md) (on a one-point grid the minimum is `p_ρ` itself); under the null law `N(X α, V)` with `Xᵀ V⁻¹ X` invertible, the minimum satisfies the [Bonferroni bound](../../../../Probability/hypothesis-testing/score-wald-and-likelihood-ratio-tests/measure-skat-omin-p-le.md) `P₀(min_ρ p_ρ ≤ t) ≤ |grid| t` for `t ∈ [0, 1]`.
