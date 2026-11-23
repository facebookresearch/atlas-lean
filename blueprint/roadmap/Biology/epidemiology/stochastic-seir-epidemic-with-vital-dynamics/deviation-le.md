# Kurtz's pathwise estimate for SEIR with vital dynamics

**Kurtz's pathwise estimate for SEIR with vital dynamics**, for every path and with explicit
constants. Let `(S, E, I, R)` be a chain path at scale `N ≥ 1` with nondecreasing birth counting
path and `(s, e, i, r)` a solution of the SEIR system with vital dynamics at scale `1`. Suppose
that on `[0, T]`

* `|s| + |e| + |i| + |r| ≤ M`, and
* every scaled driving count stays within `η` of the identity on the clock range:
  `|y_c(N a) / N - a| ≤ η` for `a ∈ [0, (rateBound (K + 2 M + 1) + 1) T]`, where
  `K ≥ (S(0) + E(0) + I(0) + R(0)) / N + μ T + η`.

Then on `[0, T]`

`deviation ≤ (initial deviation + 11 η) e^{11 (β (K + 3 M + 1) + σ + γ + μ) t}`.

Proof: the birth count bounds the total (`total_le`), so every scaled count is at most `K` and the
deviation at most `K + M` on `[0, T]`. The whole path therefore lies in the tube of radius
`K + M + 1` around the ODE solution, on which the scaled propensities are bounded by
`rateBound (K + 2 M + 1)` and Lipschitz with constant `β (K + 3 M + 1) + σ + γ + μ`
(`abs_scaledRate_sub_le`). Gronwall inside the tube
(`StochasticCRNLLN.IsChainPath.deviation_le_of_tube`, with `Z = stoichNorm network = 11`) gives
the bound.
