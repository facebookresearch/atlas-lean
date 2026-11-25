# Water fractional flow with quadratic relative permeabilities

For oil and water viscosities `μo` and `μw` and a normalized water saturation `s`, the water
fractional flow is `f(s) = μo * s ^ 2 / (μo * s ^ 2 + μw * (1 - s) ^ 2)`, from the relative
permeabilities `s ^ 2` (water) and `(1 - s) ^ 2` (oil). It is defined for all real `μo`, `μw` and
`s`: with the convention `x / 0 = 0` it is `0` where the denominator vanishes, which never happens
for positive viscosities. The intended domain is `μo > 0`, `μw > 0` and `0 ≤ s ≤ 1`.
