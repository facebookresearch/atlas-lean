# Potential outcomes and causal identification

## Finite-population randomization inference (Neyman 1923)

- [Sample mean over a set of units](sample-mean.md)
- [Sample variance over a set of units](sample-var.md)
- [Mean of a finite population](pop-mean.md)
- [Variance of a finite population](pop-var.md)
- [Finite-population average treatment effect](ate.md)
- [Difference-in-means estimator](diff-in-means.md)
- [Neyman's variance estimator](neyman-var.md)
- [Expectation of a statistic under complete randomization](rand-exp.md)
- [Unbiasedness of the difference in means under complete randomization](rand-exp-diff-in-means.md)
- [Variance of the difference in means under complete randomization](rand-exp-sq-diff-in-means-sub-ate.md)
- [Expectation of Neyman's variance estimator under complete randomization](rand-exp-neyman-var.md)
- [Neyman's variance estimator is conservative](rand-var-le-rand-exp-neyman-var.md)

## Observed outcomes, propensity score and strong ignorability

- [Observed outcome from potential outcomes](observed.md)
- [Propensity score](propensity.md)
- [Conditional independence given a discrete variable](cond-indep-discrete.md)
- [Strong ignorability](strongly-ignorable.md)
- [Strong ignorability passes to functions of the potential outcomes](comp.md)
- [The propensity score is a balancing score](cond-indep-discrete-propensity.md)
- [Calibration of the propensity score](propensity-propensity.md)
- [Characterisation of balancing scores](cond-indep-discrete-comp-iff.md)
- [Strong ignorability given a balancing score](comp-of-balancing.md)
- [Strong ignorability given the propensity score](strongly-ignorable-propensity.md)
- [Inverse probability weighting for the treated mean](integral-ipw-treated.md)
- [Inverse probability weighting for the control mean](integral-ipw-control.md)
- [Identification of the average treatment effect by inverse probability weighting](integral-ipw-ate.md)

## Inverse probability weighting with a general covariate

- [Inverse probability weighting with a general covariate](integral-ipw-treated-cond-exp.md)
- [Inverse probability weighting equals standardization](inverse-probability-weighting-equals-standardization.md)

## Potential outcomes and the local average treatment effect

- [Compliance types of Angrist, Imbens and Rubin](compliance-type.md)
- [Compliance type of a pair of potential treatments](compliance-type-2.md)
- [Potential-outcomes model with binary instrument and treatment](potential-outcomes.md)
- [Observed treatment in a potential-outcomes model](observed-treatment.md)
- [Observed outcome in a potential-outcomes model](observed-outcome.md)
- [Compliance type of a unit](type.md)
- [Compliers in a potential-outcomes model](compliers.md)
- [Independence assumption for an instrument](independence.md)
- [Exclusion restriction for an instrument](exclusion.md)
- [Monotonicity assumption (no defiers)](monotonicity.md)
- [Mean of a variable within an instrument arm](arm-mean.md)
- [Observed treatment as a 0-1 real variable](treated.md)
- [Wald instrumental-variable estimand](wald-estimand.md)
- [First stage: treatment-rate difference equals complier share](arm-mean-treated-sub.md)
- [Reduced form: outcome difference is the complier-weighted effect](arm-mean-outcome-sub.md)
- [Unrestricted algebraic identity behind the LATE theorem](wald-estimand-eq-late-totalized.md)
- [Local average treatment effect theorem](wald-estimand-eq-late.md)

## Truncated endpoints at a horizon

- [Event time truncated at a horizon](truncated-endpoint.md)
- [An event time at or before the horizon is its own truncated endpoint](truncated-endpoint-eq-of-le.md)
- [An event time at or beyond the horizon truncates to the horizon](truncated-endpoint-eq-of-ge.md)
- [Truncation changes event times beyond the horizon](truncation-changes-value.md)

## Failures of identifying assumptions and partial identification

- [Violations of parallel trends and their dependence on the outcome scale](parallel-trends-violations-and-scale-dependence.md)
- [A discontinuous untreated mean produces a jump with no treatment effect](discontinuous-untreated-mean-in-regression-discontinuity.md)
- [Worst-case bounds for a mean with missing outcomes](worst-case-bounds-for-a-mean-with-missing-outcomes.md)
- [A defier model in which the Wald ratio is not the complier effect](wald-ratio-with-defiers.md)

## Related topics

- [Causal Bayesian networks](../../../ComputerScience/machine-learning/probabilistic-graphical-models/causal-bayesian-networks/README.md):
  graphical identification; the back-door criterion is a graphical test for conditional
  ignorability.
- [Structural causal models and counterfactuals](../../../ComputerScience/machine-learning/probabilistic-graphical-models/structural-causal-models-and-counterfactuals/README.md):
  potential outcomes defined as solutions of submodels, with consistency as a theorem.
