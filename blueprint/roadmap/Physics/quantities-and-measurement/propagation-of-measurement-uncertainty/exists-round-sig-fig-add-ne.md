# Rounding is not an uncertainty calculus

Rounding `a` and `b` to one significant figure, adding, and rounding the sum can report a different
value from rounding the exact sum `a + b`. Witness: `a = b = 1.4`, where `1 + 1 = 2` is reported but
`1.4 + 1.4 = 2.8` rounds to `3`. Significant figures are reporting only, never a substitute for the
first-order law of propagation of uncertainty.
