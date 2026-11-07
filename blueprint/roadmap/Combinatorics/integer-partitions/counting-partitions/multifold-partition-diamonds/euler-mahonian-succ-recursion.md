# Recursion for the Euler–Mahonian polynomials

For every commutative ring $R$, every
natural number $d \ge 1$ and all $x, y \in R$, the Euler–Mahonian polynomials $E_d$ and
$E_{d+1}$ satisfy

$$(1 - y) E_{d+1}(x, y) = (1 - x y^{d+1}) E_d(x, y) - y (1 - x) E_d(xy, y).$$

Together with $E_1 = 1$, this says that the Euler–Mahonian polynomials are the
Dockery–Jameson–Sellers–Wilson polynomials $F_d$, defined by $F_1 = 1$ and
$F_d(q_0, w) = \bigl((1 - q_0 w^d) F_{d-1}(q_0, w) - w (1 - q_0) F_{d-1}(q_0 w, w)\bigr)/(1 - w)$
for $d \ge 2$: since $1 - w$ is a nonzerodivisor in $\mathbb{Z}[q_0, w]$, the recursion is
stated multiplied by $1 - w$.

## Sources

- Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds Revisited*, INTEGERS 26 (2026), Article A13, Theorem 1 (`integers-2026-A13-thm-1`) with recursion (1).
