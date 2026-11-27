# Evolutionarily stable behavior strategy of a role game

For finite sets `ι` and `κ`, a real `ρ` and payoff matrices `A : ι × κ → ℝ` and `B : κ × ι → ℝ`, a
pair `s = (p, q)` is an evolutionarily stable behavior strategy (Selten 1980) when `p` and `q` are
[mixed strategies](../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/expectation-maximization-algorithm/is-dist.md) and every other pair `t ≠ s` of mixed strategies satisfies, for the
[role-game payoff](role-payoff.md) `E`, either `E(t, s) < E(s, s)`, or `E(t, s) = E(s, s)` and
`E(t, t) < E(s, t)`.
