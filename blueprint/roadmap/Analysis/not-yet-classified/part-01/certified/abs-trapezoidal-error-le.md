# Trapezoidal rule error bound

If `f` is `C²` on `[[a, b]]` and `|f''| ≤ ζ` on `[[a, b]]`,
then the composite trapezoidal rule with `N` subintervals has error at most
`|b - a| ^ 3 * ζ / (12 * N ^ 2)`. Mathlib's `trapezoidal_error_le_of_c2` assumes the derivative
bound at every real point; here it is needed only on the interval.
