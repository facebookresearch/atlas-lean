# Mean time as a sum of sojourn times

**Mean time as a sum of sojourn times** (the identity behind Maruyama and Kimura 1975). For
a jointly measurable family of transition densities `w p x t ≥ 0` on `(0, 1)` satisfying the
Chapman–Kolmogorov equation for positive times,
`∫₀^∞ t w(p, x, t) dt = ∫₀¹ Ψ(p, y) Ψ(y, x) dy` with `Ψ(p, x) = ∫₀^∞ w(p, x, t) dt`, in
`ℝ≥0∞`. Dividing by `Ψ(p, x)` reads `∫₀¹ Ψ(p, y) Ψ(y, x) / Ψ(p, x) dy` (the integral of
`ageDensity` when `Ψ = selectionGreen σ`) as a mean time. The statement is abstract: no
diffusion is constructed, and `w` is not required to be the Wright–Fisher transition density.
