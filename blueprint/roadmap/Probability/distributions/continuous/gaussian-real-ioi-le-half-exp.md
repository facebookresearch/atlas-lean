# Standard-normal upper-tail bound

For `0 ≤ u`, the mass of `(u, ∞)` under the
standard normal law `gaussianReal 0 1` is at most `Real.exp (-u ^ 2 / 2) / 2`. On `(u, ∞)` the
standard density is at most `Real.exp (-u ^ 2 / 2)` times the density of `gaussianReal u 1`, which
gives `(u, ∞)` mass `1 / 2`.
