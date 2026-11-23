# Is MLE

`est` is a **maximum-likelihood estimator** for the model `law` given frequency estimates
`freq`: for every `n` and `ω`, `est n ω` maximizes `logLik law (freq n ω)` over the whole
parameter space. With `freq = empiricalFreq X` this is the MLE of the sample.
