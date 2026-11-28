# The `n`-th prime is asymptotic to `n log n`

With the zero-based indexing of
`Nat.nth Nat.Prime` (so `Nat.nth Nat.Prime 0 = 2`), the `n`-th prime, cast to `ℝ`, is
asymptotically equivalent to `n * Real.log n` along `atTop`. This is the prime number theorem
composed with `Nat.nth Nat.Prime`.
