# Nb Joint Log Lik

The joint negative binomial log-likelihood in `(β, θ)` with design `X`, fixed offset `o` and
counts `y`: `∑ᵢ nbLogPmf θ yᵢ ((X β)ᵢ + oᵢ)`. For `θ > 0` it is `∑ᵢ log NB(yᵢ; θ, μᵢ)`
(`log_negBinomialReal_exp_eq_nbLogPmf`), the shape included.
