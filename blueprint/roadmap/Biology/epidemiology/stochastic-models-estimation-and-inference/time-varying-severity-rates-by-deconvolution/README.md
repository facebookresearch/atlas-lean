# Time-varying severity rates by deconvolution

Severity rates such as case-fatality or hospitalization-fatality rates relate counts of primary events (cases, hospitalizations) to later secondary events (deaths) through a delay distribution. Modeling each primary event as an independent Bernoulli trial with a time-varying success probability gives an exact Poisson-binomial convolution model, which is accurately approximated by a Poisson likelihood and has only weak negative dependence between successive days, supporting penalized deconvolution estimators of the severity curve.

- [Poisson-binomial convolution model for secondary events and its weak dependence](poisson-binomial-convolution-model-for-secondary-events.md)
