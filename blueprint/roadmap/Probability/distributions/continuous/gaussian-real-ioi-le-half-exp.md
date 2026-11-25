# Standard-normal upper-tail bound

For `0 ≤ u`, the mass of `(u, ∞)` under the
standard normal law `gaussianReal 0 1` is at most `Real.exp (-u ^ 2 / 2) / 2`. The proof compares
densities after shifting by `u`, then uses the half-line mass `1 / 2` at zero.
