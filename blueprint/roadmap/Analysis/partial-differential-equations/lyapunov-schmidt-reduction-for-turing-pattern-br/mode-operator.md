# The linearized Turing operator on Neumann-mode coefficients

On `[0, ℓ]` with Neumann
boundary conditions, a field `u(x) = ∑ₙ cos(kₙ x) wₙ` (`wₙ ∈ ℝ²`) is mapped by the linearization
`u ↦ D u_xx + J u` to `∑ₙ cos(kₙ x) (J - kₙ² D) wₙ`; on the coefficients this is the block-diagonal
operator `wₙ ↦ (J - kₙ² D) wₙ`. Here `ι` indexes a finite set of modes with wavenumbers `κ`
(e.g. `κ n = neumannWavenumber ℓ n`, `n < N`: a Galerkin truncation).
