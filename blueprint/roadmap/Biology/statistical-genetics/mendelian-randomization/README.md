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

## Median-based estimators robust to invalid instruments

- [Simple median Mendelian randomization estimator](simple-median-mr-estimator.md)
- [Weighted median Mendelian randomization estimator](weighted-median-mr-estimator.md)
- [Consistency of the weighted median MR estimator under a valid-weight margin](weighted-median-mr-consistency-under-a-valid-weight-margin.md)
- [Penalized weighted median Mendelian randomization estimator](penalized-weighted-median-mr-estimator.md)

## Potential outcomes and the local average treatment effect

See [potential outcomes and the local average treatment effect](../../../Probability/nonparametric-survival/potential-outcomes-and-causal-identification/README.md#potential-outcomes-and-the-local-average-treatment-effect) in Probability.

## Further topics

- [Causal network pruning by MR-separation](causal-network-pruning-by-mr-separation/README.md)
- [Expression QTLs, trait networks and root causal genes](expression-qtls-trait-networks-and-root-causal-genes/README.md)
- [Focused instrument selection in Mendelian randomization](focused-instrument-selection-in-mendelian-randomization/README.md)
- [Mendelian randomization causal networks](mendelian-randomization-causal-networks/README.md)
- [Nonparametric bounds in two-sample Mendelian randomization](nonparametric-bounds-in-two-sample-mendelian-randomization/README.md)
- [Reverse two-stage least squares](reverse-two-stage-least-squares/README.md)
- [Selection bias in two-sample Mendelian randomization](selection-bias-in-two-sample-mendelian-randomization/README.md)
- [Time-varying Mendelian randomization](time-varying-mendelian-randomization/README.md)
- [Winner's-curse-free Mendelian randomization](winner-s-curse-free-mendelian-randomization/README.md)
## Correlated cis-instruments
- [Cis-Mendelian randomization with correlated instruments](cis-mendelian-randomization-with-correlated-instruments/README.md)
- [Median-initialized adaptive Lasso for some invalid instruments](median-initialized-adaptive-lasso-for-some-invalid-instruments.md)
- [MR-SPLIT cross-fitted exposures for one-sample Mendelian randomization](mr-split-cross-fitted-exposures-for-one-sample-mendelian-randomization.md)
- [Bidirectional Mendelian randomization with correlated pleiotropy](bidirectional-mendelian-randomization-with-correlated-pleiotropy/README.md)
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
- [Cochran's Q heterogeneity statistic for the IVW estimator](cochran-q-ivw-heterogeneity.md)
- [Rücker's Q′ for MR-Egger and the Q − Q′ comparison](rucker-q-egger-heterogeneity.md)
- [MR-PRESSO: leave-one-out residual tests for horizontal pleiotropy](mr-presso-leave-one-out-residual-tests.md)
- [CAUSE model of correlated and uncorrelated pleiotropy](cause-summary-statistic-model.md)
- [CAUSE marginal likelihood as a bivariate normal scale mixture](cause-marginal-likelihood.md)
- [MR-Horse: Bayesian summary-data Mendelian randomization with correlated pleiotropy and a horseshoe prior](mr-horse-bayesian-model-with-correlated-pleiotropy.md)
- [Multivariable inverse-variance weighted and MR-Egger estimators](multivariable-mr-ivw-and-egger.md)
- [Majority-type sufficient condition for identifying multivariable Mendelian randomization](multivariable-mr-identification-condition.md)
- [Identifiability of multivariable Mendelian randomization under a plurality rule](multivariable-mr-plurality-identifiability.md)
- [MVMR-Median: least absolute deviations Mendelian randomization](multivariable-mr-median-lad.md)
- [Multivariable constrained maximum likelihood (MVMR-cML) and its BIC consistency](multivariable-mr-constrained-maximum-likelihood.md)
- [Within-family Mendelian randomization](within-family-mendelian-randomization.md)
- [Point identification under a budget of invalid instruments](point-identification-under-a-budget-of-invalid-instruments.md)
- [Delta-method and Fieller intervals for the instrumental-variable ratio estimate](fieller-and-delta-method-intervals-for-the-ratio-estimate.md)
- [Generalized summary-data-based Mendelian randomization (GSMR)](gsmr-generalized-summary-data-mendelian-randomization.md)
- [HEIDI-outlier test for pleiotropic instruments](heidi-outlier-test-for-pleiotropic-instruments.md)
- [LIML, GMM and structural mean model estimators of a causal effect](liml-gmm-and-structural-mean-model-estimators.md)
- [Mediation decomposition in summary-data Mendelian randomization](mendelian-randomization-mediation-decomposition.md)
- [MR-BMA: Bayesian model averaging for multivariable Mendelian randomization](mr-bma-bayesian-model-averaging-for-multivariable-mr.md)
- [MRMix normal-mixture Mendelian randomization estimator](mrmix-normal-mixture-estimator.md)
- [Multi-trait conditional analysis from summary data (mtCOJO)](mtcojo-multi-trait-conditional-analysis-from-summary-data.md)
- [Principal-component IVW estimator for many correlated instruments](principal-component-ivw-estimator-for-correlated-instruments.md)
- [Adjusted Cochran's Q for pleiotropy in multivariable Mendelian randomization](adjusted-cochran-q-for-pleiotropy-in-multivariable-mr.md)
- [Conditional instrument strength in multivariable Mendelian randomization](conditional-instrument-strength-in-multivariable-mr.md)
- [Exact-weight IVW estimator and the generalized Cochran's Q beyond the NOME assumption](exact-weight-ivw-and-generalized-cochran-q.md)
- [Generalized inverse-variance-weighted estimator for correlated instruments](generalized-ivw-estimator-for-correlated-instruments.md)
- [Measurement-error sensitivity of the Steiger direction](measurement-error-sensitivity-of-the-steiger-direction.md)
- [MR Steiger test of causal direction](mr-steiger-test-of-causal-direction.md)
- [Multivariable Mendelian randomization: summary-data likelihood and direct effects](multivariable-mr-summary-data-likelihood-and-direct-effects.md)
- [Regression dilution of MR-Egger and the $I^2_{GX}$ statistic](regression-dilution-of-mr-egger-and-the-i2-gx-statistic.md)
- [Sample-overlap bias in two-sample Mendelian randomization](sample-overlap-bias-in-two-sample-mendelian-randomization.md)
- [SIMEX correction of the MR-Egger slope](simex-correction-of-mr-egger.md)
- [Summarized-data allele score estimator](summarized-data-allele-score-estimator.md)
