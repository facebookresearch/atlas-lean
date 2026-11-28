# Rounding modes

The four rounding-direction attributes that IEEE 754-2019 requires an
implementation of binary arithmetic to provide: round to nearest with ties to even, the default, and
the three directed rounding modes, toward $+\infty$, toward $-\infty$ and toward zero. The standard
also defines round to nearest with ties away from zero, which it requires only for decimal formats;
this model does not include it.

## Sources

- IEEE Std 754-2019, Clause 4.3.3; Goldberg, *What every computer scientist should know about floating-point arithmetic*, ACM Computing Surveys 23(1), 1991, Section 2.3.2.
