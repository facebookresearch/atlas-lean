# Positive Equilibrium

The equilibrium formula
`positiveEquilibrium r a c = (r log r / ((r - 1) a c), log r / a)`.

It is defined for all real `r`, `a`, `c` with Lean's total conventions: `Real.log` is the natural
logarithm with `log 0 = 0` and `log x = log |x|` for `x < 0`, and division by zero returns `0`.
So when `r = 1`, `a = 0` or `c = 0` the host coordinate is `0`, and when `a = 0` the parasitoid
coordinate is `0`. In the regime `r > 1`, `a > 0`, `c > 0` it is the unique fixed point of
`step r a c` in the positive quadrant (`positiveEquilibrium_spec`,
`eq_positiveEquilibrium_of_isFixedPt`).
