# Antithetic control of unimolecular networks

**Antithetic control of unimolecular networks** (Briat–Gupta–Khammash 2016, Theorem 2). Let
`net` be an open-loop network (propensities nonnegative, and positive only where the jump stays
in `ℕ^{d+1}`) with state space `𝒮 ⊆ ℕ^{d+1}`: nonempty, closed under open-loop
steps and under the actuation (adding one molecule of `X_1`, index `0`), so that `𝒮 × ℕ × ℕ` is
closed under every closed-loop transition, and irreducible (every state of `𝒮` reaches every
other by open-loop steps). Suppose
`net` is unimolecular on `𝒮`: `prop j x = ∑_i W j i * x i + w₀ j` for `x ∈ 𝒮`, with `w₀ j ≥ 0`.
Let `S` be the stoichiometry matrix and `A = S W`. Assume `A` is Hurwitz stable, the output
controllability condition `A⁻¹ ℓ 0 ≠ 0` holds, and the set-point `μ/θ` (with `μ, θ > 0`) is
accessible: some `c > 0` and `v` with positive entries have `(vᵀ (A + c I))_j < 0` for every `j`
and `vᵀ S w₀ / (c v_ℓ) < μ/θ`. Then for all `η, k > 0` the closed loop is ergodic on `𝒮 × ℕ × ℕ`,
and every jump–hold realization of it started in `𝒮 × ℕ × ℕ` satisfies `E[X_ℓ(t)] → μ/θ`,
`E[X(t)] → limX A (S w₀) k z` coordinatewise and `E[Z_1(t)] → z` with
`z = limZ1 A (S w₀) μ θ k ℓ = -(μ/θ + (A⁻¹ S w₀)_ℓ)/(k A⁻¹ ℓ 0)` and
`limX A (S w₀) k z = -A⁻¹ (S w₀ + k z e_1)`, the solution of the stationary first-moment equations
`0 = A m + S w₀ + k z e_1`, `m_ℓ = μ/θ`. (The source's displayed limits omit `S w₀` and `k`; they
agree with these when `S w₀ = 0` and `k = 1`.)

## Sources

- C. Briat, A. Gupta, M. Khammash, Cell Systems 2 (2016) 15–26, Theorem 2.
