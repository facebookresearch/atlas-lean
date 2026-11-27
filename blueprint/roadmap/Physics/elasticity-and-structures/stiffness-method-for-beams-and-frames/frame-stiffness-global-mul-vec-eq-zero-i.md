# Kernel of the global frame stiffness matrix

For `EA > 0`, `EI > 0`, `L > 0` and real `c`, `s` with `c² + s² = 1`, and every `d ∈ ℝ⁶`, the
[global frame stiffness](frame-stiffness-global.md) `K_g = Tᵀ K_f T` satisfies `K_g d = 0` if and
only if `T d = a (1, 0, 0, 1, 0, 0) + b (0, 1, 0, 0, 1, 0) + w (0, 0, 1, 0, L, 1)` for some real
`a`, `b` and `w`: the local displacement is a local rigid mode.
