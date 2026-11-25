# Nearest lattice points exist: the Wigner–Seitz translates cover space

Let `Λ` be a [Bravais lattice](../bravais-lattices/bravais-lattice.md) with basis matrix `B`, whose
columns are the primitive vectors `a₁`, `a₂`, `a₃` (so `det B ≠ 0`). For every `x ∈ ℝ³` there is a
vector `R₀` of the [lattice](../bravais-lattices/lattice.md) with `‖x - R₀‖ ≤ ‖x - R‖` for every
lattice vector `R`. Such a nearest point need not be unique. Equivalently, `x - R₀` lies in the
[Wigner–Seitz cell](wigner-seitz-cell.md) `W = {y : ‖y‖ ≤ ‖y - R‖ for every lattice vector R}`
(closed: ties included), since `R ↦ R₀ + R` maps the lattice onto itself: the translates `R + W`,
`R` in the lattice, cover all of space.
