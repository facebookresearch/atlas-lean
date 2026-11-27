# Gallager's bound on the error indicator

For a code $C = (x_1, \dots, x_M)$, a message $m$, an output $y$ and $\rho \ge 0$, with
$s = 1/(1 + \rho)$,

$$W^N(y \mid x_m)\, \mathbf 1\big[\exists\, m' \ne m,\ W^N(y \mid x_m) \le W^N(y \mid x_{m'})\big] \le W^N(y \mid x_m)^{s} \Big(\sum_{m' \ne m} W^N(y \mid x_{m'})^{s}\Big)^{\rho}.$$

This is Gallager's bound (6) on the error indicator, multiplied by $W^N(y \mid x_m)$ so that no
division by a zero probability occurs. Gallager takes $\rho > 0$; the case $\rho = 0$ is included
here (the indicator is at most $1$).

## Informally uses

- [The inequality behind Gallager's bound (6)](le-rpow-mul-sum-rpow.md)

## Sources

- R. G. Gallager, "A simple derivation of the coding theorem and some applications", IEEE Trans. Inform. Theory IT-11(1):3–18, January 1965, equations (6) and (7).
