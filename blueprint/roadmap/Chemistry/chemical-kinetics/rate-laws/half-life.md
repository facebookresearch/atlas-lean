# Half-life of each rate-law model

Half-life of each model: `[A]₀ / (2k)`, `ln 2 / k`, `1 / (2k[A]₀)` and `1 / (k[A]₀)`.
Meaningful for `k > 0` and `[A]₀ > 0`, which `halfLife_correct` and
`halfLife_indep_iff_first_order` assume; outside that domain Lean's division returns junk
values.
