# Identity-by-descent recursion in Wright's island model

One generation of Wright's island-model identity-by-descent recursion for a deme of `M`
gene copies (`M = 2N` for `N` diploids) receiving a fraction `m` of migrants from an infinite
pool: `F' = (1 - m) ^ 2 * (1 / M + (1 - 1 / M) * F)`. Biologically meaningful for `M ≥ 2`
and `0 ≤ m ≤ 1`; `M = 1` is an algebraic extension (no pair of distinct copies exists), and at
`M = 0` Lean's `1 / 0 = 0` gives a junk value.
