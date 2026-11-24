# Ballistic Velocity of ode

Derivation from the equations of motion: for `H ≠ 0`, `β > 0` and a downward path,
`sin γ > 0`, if on the window `[t₀, t₁]`, `t₀ ≤ t₁`, the altitude and speed satisfy
`h' = -v * sin γ` and `v' = -ρ(h) * v ^ 2 / (2 * β)` with entry state `h(t₀) = he`,
`v(t₀) = ve`, then `v(t) = ballisticVelocity (h(t))` throughout the window. The proof does not use
`t₀ ≤ t₁`; the hypothesis excludes the empty window, on which the statement says nothing.
