# Nb Log Lik

The negative binomial log-link log-likelihood in `β`, up to the `β`-free constant
`∑ᵢ (log (θ⁽ʸⁱ⁾ / yᵢ!) + θ log θ)` (`log_negBinomialReal_exp`): `∑ᵢ nbKernel θ yᵢ ηᵢ` with linear
predictor `ηᵢ = (X β)ᵢ + oᵢ`, known shape `θ`, design `X`, fixed offset `o` and responses `y`.
