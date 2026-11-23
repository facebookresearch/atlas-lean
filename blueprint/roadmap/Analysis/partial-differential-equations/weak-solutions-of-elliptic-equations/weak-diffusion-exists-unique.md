# Weak solutions of steady diffusion on (0, 1) exist and are unique

Let the diffusivity `κ` be almost everywhere measurable on `[0,1]` with
`0 < k_min ≤ κ ≤ k_max` almost everywhere on `[0,1]`, and let the source `f` be in `L²(0,1)`.
The steady diffusion problem `-(κ u')' = f` on `(0,1)`, `u(0) = u(1) = 0`, has a weak solution
in [`H¹₀(0,1)`](weak-h10.md), the functions with `u(x) = ∫₀ˣ u'(t) dt` on `[0,1]` for a weak
derivative `u' ∈ L²(0,1)`, and `u(1) = 0`: some such `u` satisfies `∫₀¹ κ u' v' = ∫₀¹ f v` for every
`v ∈ H¹₀(0,1)`. Every other `H¹₀(0,1)` function satisfying the same equations agrees with `u` on
`[0,1]`. The problem has no drift or zeroth-order term.
