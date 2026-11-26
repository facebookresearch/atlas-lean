# Bounded imaginary-power coordinate on the real axis

For `t : ℝ`,
`imaginaryPowerCoordinate t : BoundedMeasurableFunction ℝ` has value `r ↦ exp(i t log r)`
and supremum norm one. The real logarithm is total, with `log 0=0`; for `r>0` the value is
`r^(it)`.

The total real logarithm satisfies `Real.log 0=0` and `Real.log r=Real.log |r|` for `r<0`.
The multiplier is therefore 1 at zero and `exp(i t log |r|)` at negative arguments.
