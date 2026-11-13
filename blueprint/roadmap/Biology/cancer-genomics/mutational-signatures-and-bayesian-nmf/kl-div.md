# Generalized Kullback–Leibler divergence

The Kullback–Leibler `β = 1` divergence `d(x | y) = x log (x / y) - x + y` (Tan–Févotte,
Eq. 4). With Mathlib's `0 * log _ = 0` it gives `d(0 | y) = y`, the correct value; `y > 0` is
needed when `x > 0`.
