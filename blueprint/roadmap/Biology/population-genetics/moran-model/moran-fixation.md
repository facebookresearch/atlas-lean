# Fixation probability of the Moran process

The fixation probability of the Moran process started from `i` mutants out of `N`:
`(1 - r⁻¹ ^ i) / (1 - r⁻¹ ^ N)` for `r ≠ 1`, and `i / N` in the neutral case `r = 1`.
The model's domain is `0 < r`, `N ≥ 1`, `i ≤ N`; outside it the value is the closed formula
evaluated with Lean's total division (e.g. `x / 0 = 0`) and carries no meaning.
