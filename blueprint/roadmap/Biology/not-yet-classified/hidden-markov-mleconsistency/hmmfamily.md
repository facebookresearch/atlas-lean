# Finite hidden Markov model family

On `r` hidden states and `K` symbols, over a parameter
set `Θ ⊆ ℝ^p`: transition weights `P θ`, emission weights `e θ` and initial weights `π θ`, which
may be any reals (all zero, for example). `HMMFamily.Regular` assumes that on `Θ` they are
positive transition and emission probabilities and a stationary initial probability vector,
continuous in `θ`.
