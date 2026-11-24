# Dft Matrix

Normalized DFT matrix on `Fin d` with sign `s : ℤ`.
Entry `i, j` is `exp (2 * π * I * s * i * j / d) / √d`. For `d = 0`
the value is `0` (field division by zero), but unitary lemmas require `0 < d`.
