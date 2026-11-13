# Waterman's recursion

**Waterman's recursion** for the number `S_m(n)` of secondary structures on `n` points
with minimum hairpin `m` when every pair is allowed: `S(0) = 1` and
`S(n + 1) = S(n) + ∑_{m ≤ k < n} S(k) S(n - 1 - k)` (Waterman 1978; Stein–Waterman 1979).
For `m = 0` these are the Motzkin numbers (`watermanNumber_zero_eq_motzkinNumber`); for `m = 1`
the Stein–Waterman numbers `1, 1, 1, 2, 4, 8, 17, 37, …` (OEIS A004148).
