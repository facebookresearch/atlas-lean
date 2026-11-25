# Case-control conversion factor of Lee et al.

For a real threshold `t` and a real case fraction `P`, the case-control conversion factor of Lee,
Wray, Goddard and Visscher (2011) is

`K² (1 - K)² / (P (1 - P) z²)`,

with the [prevalence](prevalence.md) `K = K(t)` and the
[standard normal density at the threshold](threshold-density.md) `z = z(t)`. It is intended for case
fractions `0 < P < 1`. It is defined for every real `P`: with the convention `x / 0 = 0` it is `0`
at `P = 0` and at `P = 1`, and it is negative for `P < 0` and for `P > 1`.
