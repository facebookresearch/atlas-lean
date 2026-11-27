# For σ, γ > 0 and β ≥ 0, F − V is Hurwitz exactly when β < γ

Let `β ≥ 0` and `σ, γ > 0`. The infected-block Jacobian at the disease-free equilibrium (when
`N ≠ 0`),

`F - V = [[0, β], [0, 0]] - [[σ, 0], [-σ, γ]]`

(rows listed in order), is
[Hurwitz](../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/is-hurwitz.md),
that is, every complex eigenvalue of it has negative real part, if and only if `β < γ`, that is, if
and only if `R₀ = β / γ < 1` ([the SEIR next-generation matrix](r0-eq.md), with the
[threshold for the linearized infected subsystem](../next-generation-matrix-and-the-basic-reproductio/is-hurwitz-sub-iff-r0-lt-one.md)).
This is a statement about the linearization only, not a stability theorem for the closed model.
