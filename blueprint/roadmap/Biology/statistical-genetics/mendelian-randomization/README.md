# Mendelian randomization

## Wald covariance identities in an observational linear moment model

- [Linear moment model for instrumental variables](linear-moment-model.md)
- [Covariance with the outcome in a linear moment model](covariance-outcome.md)
- [Wald ratio identity](covariance-div-covariance.md)
- [Wald ratio identity for an instrument independent of the residual](covariance-div-covariance-of-indep-fun.md)
- [Wald ratio as a ratio of regression slopes](covariance-div-variance-div.md)
- [Bias of the ordinary least-squares coefficient under confounding](covariance-div-variance.md)

## Summary-data estimators: inverse-variance weighting

- [Ratio estimate of a single SNP](ratio-estimate.md)
- [Inverse-variance weight of a ratio estimate](ivw-weight.md)
- [Inverse-variance-weighted estimator](ivw.md)
- [Weighted residual sum of squares through the origin](weighted-ssr.md)
- [IVW estimator as a weighted mean of ratio estimates](ivw-eq-weighted-mean.md)
- [IVW estimator minimizes the weighted residual sum of squares](ivw-le-weighted-ssr.md)
- [Positivity of the total IVW weight](sum-ivw-weight-pos.md)
- [IVW recovers an exact proportionality coefficient](ivw-of-proportional.md)
- [Unbiasedness of the IVW estimator](integral-ivw.md)
- [Variance of the IVW estimator](variance-ivw.md)

## MR-Egger regression and InSIDE

- [Weighted mean](weighted-mean.md)
- [Weighted covariance](weighted-cov.md)
- [MR-Egger slope](egger-slope.md)
- [MR-Egger intercept](egger-intercept.md)
- [Weighted residual sum of squares of a line](egger-ssr.md)
- [MR-Egger line is the weighted least-squares line](egger-ssr-le.md)
- [MR-Egger slope under pleiotropy](egger-slope-eq.md)
- [MR-Egger intercept under pleiotropy](egger-intercept-eq.md)
- [InSIDE identity for MR-Egger](egger-slope-eq-of-inside.md)
- [Directional pleiotropy biases the IVW estimator](ivw-of-pleiotropy.md)

## Weak instruments: the ratio estimator has no mean

- [Ratio with a Gaussian denominator has infinite first moment](lintegral-enorm-div-eq-top.md)
- [Ratio of independent normal variables is not integrable](not-integrable-div-gaussian.md)

## Potential outcomes and the local average treatment effect

See [potential outcomes and the local average treatment effect](../../../Probability/nonparametric-survival/potential-outcomes-and-causal-identification/README.md#potential-outcomes-and-the-local-average-treatment-effect) in Probability.

## Weak and invalid instruments

- [Weak-instrument bias of the two-stage least-squares estimator toward the confounded association](weak-instrument-bias-of-two-stage-least-squares.md)
- [Identification of a causal effect when some instruments are invalid](identification-with-some-invalid-instruments.md)
- [Zero modal pleiotropy assumption](zero-modal-pleiotropy-assumption.md)
- [Mode-based estimate of a causal effect](mode-based-estimate.md)
- [The sisVIVE estimator](sisvive-estimator.md)
- [MR-Lasso estimator](mr-lasso-estimator.md)
- [Contamination mixture estimator for Mendelian randomization](contamination-mixture-mr-estimator.md)
- [Constrained maximum-likelihood Mendelian randomization (cML-MR)](constrained-maximum-likelihood-mr-estimator.md)
- [cML-MR: coordinate descent and BIC model averaging](cml-mr-coordinate-descent-and-bic-model-averaging.md)
- [Profile-likelihood Mendelian randomization estimator under many weak instruments](mr-profile-likelihood-estimator-under-weak-instruments.md)
- [Adjusted profile score for Mendelian randomization with systematic pleiotropy](mr-raps-adjusted-profile-score.md)
- [Likelihood-based summary-data Mendelian randomization with correlated variants](likelihood-based-summary-data-mr-with-correlated-variants.md)

## Heterogeneity and pleiotropy tests

- [Cochran's Q heterogeneity statistic for the IVW estimator](cochran-q-ivw-heterogeneity.md)
- [Rücker's Q′ for MR-Egger and the Q − Q′ comparison](rucker-q-egger-heterogeneity.md)
- [MR-PRESSO: leave-one-out residual tests for horizontal pleiotropy](mr-presso-leave-one-out-residual-tests.md)

## Correlated pleiotropy

- [CAUSE model of correlated and uncorrelated pleiotropy](cause-summary-statistic-model.md)
- [CAUSE marginal likelihood as a bivariate normal scale mixture](cause-marginal-likelihood.md)
- [MR-Horse: Bayesian summary-data Mendelian randomization with correlated pleiotropy and a horseshoe prior](mr-horse-bayesian-model-with-correlated-pleiotropy.md)

## Multivariable Mendelian randomization

- [Multivariable inverse-variance weighted and MR-Egger estimators](multivariable-mr-ivw-and-egger.md)
- [Majority-type sufficient condition for identifying multivariable Mendelian randomization](multivariable-mr-identification-condition.md)
- [Identifiability of multivariable Mendelian randomization under a plurality rule](multivariable-mr-plurality-identifiability.md)
- [MVMR-Median: least absolute deviations Mendelian randomization](multivariable-mr-median-lad.md)
- [Multivariable constrained maximum likelihood (MVMR-cML) and its BIC consistency](multivariable-mr-constrained-maximum-likelihood.md)

## Within-family designs and expression-trait Mendelian randomization

- [Within-family Mendelian randomization](within-family-mendelian-randomization.md)
- [Summary-data-based Mendelian randomization (SMR) test statistic](smr-test-statistic.md)
