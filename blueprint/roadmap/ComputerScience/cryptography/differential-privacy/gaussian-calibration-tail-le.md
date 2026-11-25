# Gaussian calibration tail estimate

**Gaussian calibration tail estimate** (Dwork and Roth, *The Algorithmic Foundations of
Differential Privacy* (2014), Theorem A.1, in standardized form). Under the calibration
hypothesis `2 * Real.log ((5 / 4) / δ) < c ^ 2` and `r ≤ ε / c`, where `r` is the standardized
shift (sensitivity divided by the Gaussian noise scale) and `c` is the calibration constant, the
standard Gaussian mass above the privacy-loss threshold `ε / r - r / 2` is at most `δ`. The case
`δ ≥ 1` follows by a trivial branch.
