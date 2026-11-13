# Quad Form

The quadratic form `Q_A(x) = x ⬝ᵥ (A *ᵥ x)` of a real square matrix `A`. It has the same values
as Mathlib's `Matrix.toQuadraticForm' A`, which bundles the form as a `QuadraticForm` and needs
`DecidableEq n`; this file keeps the plain real-valued function under its MF03 name.
