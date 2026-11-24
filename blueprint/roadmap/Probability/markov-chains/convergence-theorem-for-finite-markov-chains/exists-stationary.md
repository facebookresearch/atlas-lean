# Existence of a stationary distribution

Every row-stochastic matrix on a nonempty
finite state space has a stationary probability vector `π` (`π ≥ 0`, `∑ π = 1`, `π ᵥ* P = π`).

The proof takes Cesàro averages of the rows of `Pᵏ` started from one state. They lie in the
compact box `[0,1]^S`; a subsequential limit is a probability vector, and the telescoping
identity `μₙ ᵥ* P - μₙ = (n+1)⁻¹ (rₙ₊₁ - r₀)` shows that it is stationary.
