# Tightness of `n ≥ 2K`

**Tightness of `n ≥ 2K`** (Bhaskar & Song 2014, Corollary 7): for every `K ≥ 2` there are
two piecewise-constant histories with `K` pieces whose sizes differ at some time `s ≥ 0` but
whose first-coalescence times `c_m` agree for `2 ≤ m ≤ 2K - 1`; so
`sizeFn_eq_of_firstCoalMean_eq` fails for `n = 2K - 1`. The construction is explicit: with
`z = 2^{-C(m,2)}`, the two histories have coalescent-time breakpoints `(2j - 1) log 2` and
`2j log 2`, so `C(m,2) (c_m - c'_m)` is a polynomial of degree `2K - 2` in `z`; its
coefficients are those of `∏_{m=2}^{2K-1} (X - 2^{-C(m,2)})`, which vanishes at the `2K - 2`
points and has a nonzero constant term (the sizes at time `0` differ).
