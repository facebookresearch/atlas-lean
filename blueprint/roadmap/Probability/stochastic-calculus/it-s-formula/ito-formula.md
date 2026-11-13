# Itô's formula

**Itô's formula** for Brownian motion: for a Brownian motion `B` adapted to `F` with
increments independent of the past and jointly measurable in `(t, ω)`, and `f` of class `C²`
with `|f'| ≤ C` and `|f''| ≤ C`,
`f(B t) = f(B 0) + ∫_0^t f'(B u) dB u + (1/2) ∫_0^t f''(B u) du` almost surely, for every
`t ≥ 0` (Karatzas–Shreve 1991, Theorem 3.3.3). The last integral is a pathwise Riemann integral;
it is the integral of a continuous function on almost every path.
