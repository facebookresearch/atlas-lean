# Ols H2 Hat

The **unweighted LD-score regression heritability estimator** `ĥ² = b̂ · M / N`, where `b̂` is
the ordinary (unweighted) least-squares slope of the statistics `χ` on the LD scores `ℓ` of the
`M` markers and `N` is the sample size. It is an unweighted analogue of the estimator of
Bulik-Sullivan et al. (2015), who fit the slope by weighted least squares; for finite samples the
two slopes generally differ. (Lean's `x / 0 = 0` makes it `0` when `N = 0`, and `olsSlope` is `0`
when the LD scores are all equal, where the slope is not identified.)
