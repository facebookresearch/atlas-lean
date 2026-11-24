# Rational LP point encoding a rational dispatch

For a rational generation `p` and angles `θ`, the rational encoded point is
`(max(z, 0), max(-z, 0))`, the componentwise positive parts followed by the negative parts of
`z = (p, θ)`. The rational objects copy the real ones entrywise, so that the checker is computable;
the [casting lemmas](rat-lp-matrix-map.md) identify them with the real linear program.
