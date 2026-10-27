---
article_id: af_6a3eb52aa8d73540f532bc2f
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.PrimeNumberTheorem.prime_number_theorem_chebyshev_theta_error
---

# Chebyshev Theta PNTError Wanted

Quantitative prime number theorem for the Chebyshev `θ` function: for every
real `ε > 0`, `θ(x) - x = O(x * exp(-(log x)^(3/5 - ε)))` as `x → +∞`.

This is stronger than the qualitative Chebyshev-`θ` asymptotic equivalent to the
repository's existing prime-counting `prime_number_theorem`
(i.e. `θ(x) ~ x`, vanishing relative error with no rate), and it
and this exponential asymptotic error rate is distinct from the existing
explicit polynomial-in-`log x` Dusart bounds, some global and some finite-range.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.PrimeCounting.ChebyshevThetaPNTErrorWanted](../../../../../../sources/v2/WantedExt.md)
- Julian Ransford, "A Sum of Gcd's over Friable Numbers", Journal of Integer Sequences 19 (2016), Prime Number Theorem at lines 288–292; URL: https://cs.uwaterloo.ca/journals/JIS/VOL19/Ransford/ransford2.tex complete-source SHA-256 `1675f24c7dbb411a931a2c37a36917b63494686ad03d851beb2a18814e04005d`; normalized contextual lines 288–292 SHA-256 `adb74cce8f0da6d1a60450de8ce1029a6e5de3c77e1d9b6a8de7d62dece7f8d5`; normalized theorem lines 290–292 SHA-256 `2aa08383a1b0c24261c27687f2576878a793de5885ef2f1ac841eebe4cf480bb`.
