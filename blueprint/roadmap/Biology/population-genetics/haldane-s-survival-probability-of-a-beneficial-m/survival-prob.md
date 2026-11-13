# Haldane's survival probability of a mutant

Haldane's survival probability `π(s) = 1 - q(s)` of a mutant with selective advantage `s`
per generation, whose number of copies in the next generation is Poisson with mean `1 + s`.
The model needs `s ≥ -1`; for `s < -1` the mean is truncated to `0` (`Real.toNNReal`), the
mutant leaves no copies, and `π(s) = 0`.
