# GREML and Haseman–Elston estimation of SNP heritability

## The genetic relationship matrix

- [Genetic relationship matrix](grm.md)
- [Symmetry of the genetic relationship matrix](grm-comm.md)
- [The GRM is the normalized cross product of the transposed matrix](grm-eq-ld-corr-transpose.md)
- [The genetic relationship matrix is positive semidefinite](pos-semidef-grm.md)

## Haseman–Elston regression as least squares

- [Each pair $i < j$ consists of two distinct individuals](ne-of-mem-pairs.md)
- [Haseman–Elston estimator](he-estimate.md)
- [Residual sum of squares of Haseman–Elston regression](he-rss.md)
- [Pythagoras for the Haseman–Elston residual sum of squares](he-rss-eq.md)
- [The Haseman–Elston estimator minimizes the residual sum of squares](he-rss-he-estimate-le.md)
- [Unique Haseman–Elston slope when some $A_{ij}$ with $i<j$ is nonzero](he-rss-eq-he-rss-he-estimate-iff.md)

## Phenotype moments and the Haseman–Elston identity

- [The phenotype of the LD-score model is square integrable](mem-lp-pheno.md)
- [Raw second moments of phenotypes in the LD-score model](integral-pheno-mul-pheno.md)
- [Haseman–Elston identity for distinct individuals](integral-pheno-mul-pheno-of-ne.md)
- [Haseman–Elston estimate integrates to $h^2$ if the GRM is not diagonal](integral-he-estimate.md)

## Error bounds and consistency

- [Haseman–Elston error formula when some $A_{ij}$ with $i<j$ is nonzero](he-estimate-sub.md)
- [Deviation of a phenotype cross-product from $h^2 A_{ij}$](he-dev.md)
- [Integrated squared-error bound for Haseman–Elston regression](integral-he-estimate-sub-sq-le.md)
- [Chebyshev bound for Haseman–Elston regression](measure-abs-he-estimate-sub-ge-le.md)
- [Consistency of Haseman–Elston regression](tendsto-measure-abs-he-estimate-sub-ge.md)

## REML criterion and its spectral form

- [GREML covariance matrix $\sigma_g^2 K + \sigma_e^2 I$](greml-cov.md)
- [Contrast variances $\sigma_g^2 d_i + \sigma_e^2$](contrast-var.md)
- [Spectral REML criterion for GREML variance components](spectral-log-lik.md)
- [Orthonormal error contrast diagonalizing the relationship matrix](is-spectral-contrast.md)
- [A diagonalizing orthonormal contrast is an error contrast](is-error-contrast.md)
- [Diagonalizing contrasts make the GREML contrast covariance diagonal](contrast-greml-cov.md)
- [REML log-likelihood in spectral form at positive contrast variances](reml-log-lik-greml-cov.md)
- [Orthonormal error contrasts rotate to diagonalize a symmetric matrix](exists-is-spectral-contrast.md)
- [REML log-likelihood via an orthogonal rotation, at positive variances](reml-log-lik-eq-spectral-log-lik-of-orth.md)

## REML score equations

- [REML score for the genetic variance in spectral form](score-g.md)
- [REML score for the residual variance in spectral form](score-e.md)
- [Spectral criterion's derivative in $\sigma_g^2$ at positive variances](has-deriv-at-spectral-log-lik-fst.md)
- [Spectral criterion's derivative in $\sigma_e^2$ at positive variances](has-deriv-at-spectral-log-lik-snd.md)
- [Positive contrast variances form an open set](is-open-pos-contrast-var.md)
- [Spectral score equations at a local maximizer with positive variances](score-eq-zero-of-is-local-max.md)
- [REML score equations at a local maximizer with positive variances](score-eq-zero-of-is-local-max-reml-log-l.md)
- [REML projection matrix $P = B^\top (B V B^\top)^{-1} B$](reml-proj.md)
- [REML scores in GCTA's matrix form at positive contrast variances](score-eq-reml-proj.md)
- [GCTA's REML equations at a local maximizer with positive variances](reml-equations-of-is-local-max.md)

## Mean-zero REML scores under the GREML model

- [Second moments of the rotated contrasts under the GREML model](integral-sq-contrast.md)
- [The REML score for $\sigma_g^2$ has mean zero at the true parameter](integral-score-g.md)
- [The REML score for $\sigma_e^2$ has mean zero at the true parameter](integral-score-e.md)

## Closed-form estimate for two-level spectra

- [Indices of the contrasts with a given eigenvalue](class-set.md)
- [Number of contrasts with a given eigenvalue](group-count.md)
- [Sum of squared rotated contrasts with a given eigenvalue](group-ss.md)
- [Mean squared rotated contrast with a given eigenvalue](group-mean.md)
- [Closed-form REML estimate for a two-level spectrum](two-level-reml.md)
- [Contrast variances at the closed-form estimate equal the class means](contrast-var-two-level-reml.md)
- [Closed form maximizes the spectral criterion for positive class means](is-max-on-spectral-log-lik-two-level-rem.md)
- [Closed form is the unique REML maximizer for positive class means](is-max-on-reml-log-lik-two-level-reml.md)
- [The closed-form REML estimator is unbiased when both eigenvalues occur](integral-two-level-reml.md)

## Further topics

- [Sparse two-stage SNP heritability estimation](sparse-two-stage-snp-heritability-estimation/README.md)
