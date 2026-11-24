# Kurtz's pathwise estimate for SEIR with vital dynamics

Let `β`, `σ`, `γ`, `μ` be nonnegative, let `(S, E, I, R)` be a [chain path](is-chain-path.md) at
scale `N ≥ 1` driven by functions `y_c` with nondecreasing birth path `y_birth`, and let
`(s, e, i, r)` be a
[solution of the SEIR system with vital dynamics](../global-stability-of-the-seir-model/is-solution.md)
at scale `1`. Let `T` and `M` be real, `η ≥ 0` and `K ≥ (S(0) + E(0) + I(0) + R(0)) / N + μ T + η`,
and write `B = μ + β (K + 2 M + 1)² + (σ + γ + μ) (K + 2 M + 1)` (the [common bound](rate-bound.md)
at `K + 2 M + 1`). Suppose that

- `|s(x)| + |e(x)| + |i(x)| + |r(x)| ≤ M` for every `x ∈ [0, T]`, and
- every scaled driving count stays within `η` of the identity on the clock range:
  `|y_c(N a) / N - a| ≤ η` for every channel `c` and every `a ∈ [0, (B + 1) T]`.

Then for every `t ∈ [0, T]` the [deviation](deviation.md) `D` satisfies

`D(t) ≤ (D(0) + 11 η) e^(11 (β (K + 3 M + 1) + σ + γ + μ) t)`.

The estimate holds path by path, with explicit constants.

Proof: the births bound the total ([total bound](total-le.md)), so every scaled count is at most `K`
and the deviation at most `K + M` on `[0, T]`. The path therefore stays in the tube of radius
`K + M + 1` around the solution, on which the scaled propensities are bounded by `B` and Lipschitz
with constant `β (K + 3 M + 1) + σ + γ + μ` ([Lipschitz bound](abs-scaled-rate-sub-le.md)).
Gronwall's inequality inside the tube, with the total jump size `Z = 11`
([reaction vectors](stoich-norm-network.md)), gives the bound.
