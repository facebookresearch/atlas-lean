# Fractional-flow derivative formula

For viscosities `μo` and `μw` and a normalized saturation `s`, the fractional-flow derivative is
`f'(s) = 2 * μo * μw * s * (1 - s) / (μo * s ^ 2 + μw * (1 - s) ^ 2) ^ 2`. It is defined for all
real arguments: with the convention `x / 0 = 0` it is `0` where the denominator vanishes. For
positive viscosities it is the [derivative of the fractional flow](has-deriv-at-frac-flow.md).
