# Moran Fixation

The **Moran fixation probability** `ρ₁ = (1 - 1/r) / (1 - 1/r^N)` of a single mutant of
fitness `r` in a well-mixed population of size `N`. The formula is the fixation probability for
`r > 0`, `r ≠ 1` and `N ≥ 1`. The definition is total: at `r = 1` numerator and denominator
vanish and Lean's convention `0 / 0 = 0` gives `0`, not the neutral fixation probability `1/N`
(which is the limit as `r → 1`).
