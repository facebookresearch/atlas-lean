# Concentration consumed in a first-order batch reaction

For real numbers $k$ (rate constant), $c_0$ (initial concentration) and $t$ (time), the
concentration consumed by time $t$ is

$$c_0 - c_0\, e^{-k t},$$

the initial concentration minus the explicit first-order solution $c(t) = c_0 e^{-k t}$ of a closed,
constant-volume batch reaction. It equals $\int_0^t k\, c(s)\, ds$ for all real $k$, $c_0$ and $t$,
an oriented integral when $t < 0$
([consumption under first-order decay](first-order-decay-consumption.md)). In the physical reading
$k \ge 0$, $c_0 \ge 0$ and $t \ge 0$, where it
[lies between $0$ and $c_0$](first-order-consumed-mem-icc.md); the formula is defined for all real
inputs.