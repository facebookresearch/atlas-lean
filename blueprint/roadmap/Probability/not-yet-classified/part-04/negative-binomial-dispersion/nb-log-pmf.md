# Nb Log Pmf

The full negative binomial log mass function of a count `y` under the log link, as a function
of the shape `θ` and the linear predictor `η` (mean `μ = e^η`):
`∑_{j<y} log (θ + j) - log y! + θ log θ + nbKernel θ y η`. For `θ > 0` it is
`log NB(y; θ, e^η)` (`log_negBinomialReal_exp_eq_nbLogPmf`).
