# Certified bisection bounds

Let `f` be continuous on `[a, b]` with `a ≤ b` and
`f a ≤ 0 ≤ f b`. After `n = ds.length` certified bisection steps from `[a, b]`, the returned
rational bracket has width `(b - a) / 2 ^ n`, lies in `[a, b]`, and encloses a root of `f`.
