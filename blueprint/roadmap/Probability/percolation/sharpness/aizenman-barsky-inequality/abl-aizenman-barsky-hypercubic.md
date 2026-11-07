# Aizenman–Barsky inequality on $\mathbb{Z}^d$

The Aizenman–Barsky inequality on `ℤ^d`: `∂_β M ≤ |J| M ∂_h M` with `|J| = ∑_y J_{0y}`.
Reference: M. Aizenman, D. J. Barsky, "Sharpness of the phase transition in percolation models",
Comm. Math. Phys. 108 (1987) 489–526. Scope and fidelity: this is the first Aizenman–Barsky
differential inequality `∂_β M ≤ |J| M ∂_h M` for independent bond percolation on `ℤ^d` with
nearest-neighbour, translation-invariant couplings `J ≥ 0` (edge probability `1 - e^{-βJ_e}`) and a
ghost field (ghost-edge probability `1 - e^{-h}`), for `β ≥ 0`, `h > 0`; `M(β, h)` is the
probability that the origin is connected to the ghost. Aizenman–Barsky allow general summable
translation-invariant couplings; here `J` vanishes off lattice edges. The second inequality `M ≤ h
∂_h M + M² + β M ∂_β M` (`AizenmanBarskyPDI`) is not proved here. The derivatives are Lean `deriv`s:
`M` is shown differentiable in `h`, while at a point where `β ↦ M(β, h)` is not differentiable
`deriv` is `0` and the inequality holds trivially.
