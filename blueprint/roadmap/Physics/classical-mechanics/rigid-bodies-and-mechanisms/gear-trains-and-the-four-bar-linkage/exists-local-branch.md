# Local branch of a four-bar linkage at a regular closed configuration

For a [four-bar linkage](four-bar.md) and a [closed configuration](is-closed.md) `(θ₂, θ₃, θ₄)` at
which the [dependent-angle Jacobian](dependent-jacobian.md) has nonzero determinant, there is a map
`ψ : ℝ → ℝ²` with `ψ(θ₂) = (θ₃, θ₄)` such that:

- on a neighbourhood of `(θ₂, θ₃, θ₄)`, a configuration `(θ, φ₃, φ₄)` is closed if and only if
  `ψ(θ) = (φ₃, φ₄)`;
- on a neighbourhood of `θ₂`, every `(θ, ψ(θ))` is closed;
- `ψ` has derivative at `θ₂` equal to the [velocity ratios](velocity-ratio.md) at `(θ₂, θ₃, θ₄)`.
