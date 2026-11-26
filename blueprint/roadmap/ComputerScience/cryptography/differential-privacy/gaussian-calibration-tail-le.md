# Gaussian calibration tail estimate

Let `0 < ε < 1`, `0 < δ`, `0 < c` and `0 < r`, with
`2 * Real.log ((5 / 4) / δ) < c ^ 2` and `r ≤ ε / c`. Then the standard normal law
`gaussianReal 0 1` gives mass at most `δ` to `(ε / r - r / 2, ∞)`. Here `r` is the standardized
shift (sensitivity divided by the Gaussian noise scale), `c` is the calibration constant and
`ε / r - r / 2` is the standardized privacy-loss threshold. This is a tail estimate behind the
calibration of the Gaussian mechanism in Dwork and Roth, *The Algorithmic Foundations of
Differential Privacy* (2014), proof of Theorem A.1, which asks for the bound `δ / 2` on this
one-sided tail and assumes sensitivity at least `1`; the bound here is `δ`, with no lower bound on
the sensitivity. For `δ ≥ 1` the bound holds because the mass is at most `1`.
