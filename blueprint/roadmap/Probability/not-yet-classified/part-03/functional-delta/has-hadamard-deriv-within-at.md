# Has Hadamard Deriv Within At

`φ` is **Hadamard differentiable** at `θ` with derivative `φ'`, tangentially to `E₀`, for the
domain `D`: for every `h ∈ E₀`,
`t⁻¹ • (φ (θ + t • k) - φ θ) → φ' h` as `t ↓ 0` and `k → h`, along those `(t, k)` with
`θ + t • k ∈ D`.

Equivalently, `(φ (θ + tₙ • hₙ) - φ θ) / tₙ → φ' h` for all sequences `tₙ ↓ 0`, `hₙ → h ∈ E₀`
with `θ + tₙ • hₙ ∈ D`. This is van der Vaart (1998), §20.2, except that `t` is one-sided and
`φ'` is not required to be linear (Shapiro's directional notion); the usual definition implies
this one.
