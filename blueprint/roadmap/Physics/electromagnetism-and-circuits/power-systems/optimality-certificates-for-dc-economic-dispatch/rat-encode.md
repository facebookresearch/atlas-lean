# Rational LP point encoding a rational dispatch

For a rational generation `p` and angles `θ`, the rational encoded point is
`(max(z, 0), max(-z, 0))`, the componentwise positive parts followed by the negative parts of
`z = (p, θ)`. The rational linear program that the exact checker assembles from such data casts to
the real one built from the cast data: [matrix](rat-lp-matrix-map.md),
[right-hand side](cast-vec-rat-lp-rhs.md), [objective](cast-vec-rat-lp-objective.md) and
[encoded point](cast-vec-rat-encode.md).
