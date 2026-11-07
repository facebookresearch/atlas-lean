# Ergodicity is primitivity of the transition matrix

Ergodicity is exactly primitivity of the transition matrix. This is the
bridge to Mathlib: `Matrix.IsPrimitive` is the same condition for a bare
matrix, while `IsErgodic` is the stochastic-matrix form, with nonnegativity
supplied by the `StochasticMatrix` structure.
