# Total radiated power of an axisymmetric intensity pattern

For an intensity pattern `U : ℝ → ℝ` depending only on the polar angle, the total radiated power is

`P(U) = ∫_0^{2π} ∫_0^π U(θ) sin θ dθ dφ = 2π ∫_0^π U(θ) sin θ dθ`,

the integral of `U` against the solid-angle element `sin θ dθ dφ` over the sphere. The inner
integral is `0` when `θ ↦ U(θ) sin θ` is not integrable on `[0, π]`.
