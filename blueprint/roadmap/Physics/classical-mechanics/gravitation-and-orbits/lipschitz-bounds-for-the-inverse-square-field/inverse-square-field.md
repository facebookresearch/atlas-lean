# Inverse Square Field

The inverse-square field `μ • r / ‖r‖^3` (outward radial form) on a real inner-product space, as the scalar multiple
`(μ / ‖r‖^3) • r`. It is intended for points away from the origin; at
`r = 0` the scalar factor is Lean's junk value for division by zero and
the field value is `0`. For `μ > 0` this field points parallel to
`r` (outward from the origin); the gravitational acceleration toward
an attracting body at the origin is its negative,
`-(μ / ‖r‖^3) • r`.
