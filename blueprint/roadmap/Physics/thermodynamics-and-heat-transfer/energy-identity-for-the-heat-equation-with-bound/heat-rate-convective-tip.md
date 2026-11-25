# Base heat rate of a fin with a convective tip

Let `k`, `A`, `h`, `P` and `L` be positive, and let `(T, q)` be a
[steady fin](is-fin-steady-state.md) on `[0, L]` with the convective tip condition
`q(L) = hA (T(L) - Ta)` (outward normal `+x`). Then, with `θ(x) = T(x) - Ta` and the
[fin parameter](fin-parameter.md) `m = √(hP/(kA))`,

`q(0) = √(hPkA) θ(0) (sinh(mL) + (h/(mk)) cosh(mL)) / (cosh(mL) + (h/(mk)) sinh(mL))`.
