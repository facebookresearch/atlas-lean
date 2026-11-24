# The linearization at extinction has slope c − e

For all real numbers `c` and `e`, the [balance](balance-2.md) `f(p) = c p (1 - p) - e p` has
derivative `f'(0) = c - e` at the extinction equilibrium `p = 0`. So `p = 0` is linearly unstable
(`f'(0) > 0`) exactly when `c > e` and linearly stable (`f'(0) < 0`) exactly when `c < e`; for
`c = e` the linearization is zero and decides nothing. This concerns the linearization only; for the
nonlinear equation, extinction is
[not Lyapunov stable when `0 ≤ e < c`](not-is-lyapunov-stable-zero.md) and
[globally stable on `[0, 1]` when `0 ≤ c ≤ e` and `e > 0`](extinction-is-globally-stable.md).
