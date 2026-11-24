# For 0 ≤ c ≤ e, a solution with p(0) ≥ 0 never exceeds p(0)

For real numbers `c` and `e` with `0 ≤ c ≤ e`, every [solution](is-solution-2.md) `p` of the
Levins equation `p' = c p (1 - p) - e p` with `p(0) ≥ 0` satisfies `p(t) ≤ p(0)` for all `t ≥ 0`:
the occupied fraction never exceeds its initial value. Indeed `p` is then the
[explicit solution](levins.md) started at `p(0)`, and `0 ≤ p(t) ≤ p(0) e^{(c - e) t} ≤ p(0)`.
