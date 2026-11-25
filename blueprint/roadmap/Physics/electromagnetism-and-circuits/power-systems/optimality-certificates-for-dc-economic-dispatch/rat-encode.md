# Rational LP point encoding a rational dispatch

For a rational generation `p` and angles `θ`, the rational encoded point is
`(max(z, 0), max(-z, 0))`, the componentwise positive parts followed by the negative parts of
`z = (p, θ)`. Its entries are given by the same formula as for the real linear program, over the
rationals, so that the checker is an exact finite test. The cast of the assembled rational program
is the real one: [matrix](rat-lp-matrix-map.md), [right-hand side](cast-vec-rat-lp-rhs.md),
[objective](cast-vec-rat-lp-objective.md) and [encoded point](cast-vec-rat-encode.md).
