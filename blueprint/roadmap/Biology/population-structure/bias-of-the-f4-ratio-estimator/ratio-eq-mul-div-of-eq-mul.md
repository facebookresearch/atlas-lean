# Ratio eq mul div of eq mul

Bias factor of the f4-ratio estimator, in the real-number form that the
drift-model glue instantiates with `fX = f4(A, O; X, C)`, `fY = f4(A, O; Y, C)`
and `fB = f4(A, O; B, C)`: if the numerator is `α` times the statistic of the
unsampled source `Y` (`fX = α * fY`, the conclusion of
`DriftModel.f4_admixture_right` for `X = α Y + (1 - α) C`) and the denominator
`fB` is nonzero, the ratio `fX / fB` is `α` times the factor `fY / fB`. For
`fB = 0` the ratio is undefined; Lean's value `fX / 0 = 0` is junk and is not
covered by this statement.
