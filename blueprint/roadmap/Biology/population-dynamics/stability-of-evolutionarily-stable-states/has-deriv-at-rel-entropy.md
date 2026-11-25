# Derivative of the relative entropy along a replicator solution

For a finite set `ι` of strategies, a payoff matrix `A` on `ι`, a vector `p` with `∑_i p_i = 1`, a
[solution](../replicator-dynamics/is-solution.md) `x` of the replicator equation
`x_i' = x_i ((A x)_i - x · A x)` for `t ≥ 0`, and a time `t ≥ 0` with `x_i(t) ≠ 0` for every `i`,
the [relative entropy](../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/mean-field-variational-inference/kl.md)
`V_p(x(·))`, where `V_p(y) = ∑_i p_i (log p_i - log y_i)` with `log 0 = 0` and `log z = log |z|`,
has derivative `-(p · A x(t) - x(t) · A x(t))` at `t` (Hofbauer and Sigmund 1998, proof of Theorem
7.2.4, which writes `P = ∏_i x_i^(p_i)` and `P'/P = p · A x - x · A x`).
