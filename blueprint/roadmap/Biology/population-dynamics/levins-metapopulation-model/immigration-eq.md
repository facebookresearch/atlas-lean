# Immigration equilibrium

For real `c`, `e` and `m`, the immigration equilibrium is `p̂ = 2 m / (e + m - c + √D)`, where
`D = (c - e - m)² + 4 c m` is the [discriminant](disc.md).

On the intended range `c ≥ 0`, `e ≥ 0`, `m > 0` the denominator is [positive](denom-pos.md), `p̂` is
a [zero](balance-immigration-eq.md) of the [balance](balance.md)
`f(p) = c p (1 - p) - e p + m (1 - p)`, and [`0 < p̂ ≤ 1`](immigration-eq-mem-ioc.md). There, for
`c > 0` it is the [quadratic-formula root](immigration-eq-eq-quadratic.md)
`(c - e - m + √D) / (2 c)` in rationalized form, and for `c = 0` it is `m / (e + m)`.

The formula is defined for all real inputs, with the conventions `√x = 0` for `x < 0` (a negative
`D` needs `c m < 0`) and `x / 0 = 0`, so a zero denominator gives `p̂ = 0`. Outside the intended
range `p̂` need not be a zero of the balance. At `m = 0` the formula gives `p̂ = 0`, the extinction
equilibrium, even when `c > e`; for `c > 0` and `e ≥ 0` its
[limit as `m` decreases to `0`](tendsto-immigration-eq-zero.md) is `max(1 - e / c, 0)`.
