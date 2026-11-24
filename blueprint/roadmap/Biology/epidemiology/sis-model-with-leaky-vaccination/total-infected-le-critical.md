# At Rᵥ = 1 the total infected obeys an algebraic bound

Let $\beta \ge 0$, $\gamma > 0$, $0 \le \varepsilon \le 1$ and $N > 0$, and let
$(S_u, I_u, S_v, I_v)$ be a [solution](is-solution.md) of the SIS model with leaky vaccination, with
transmission rate $\beta$, recovery rate $\gamma$, vaccine efficacy $\varepsilon$ and population
size $N$, with group sizes $S_u(0) + I_u(0) = (1 - p) N$ and $S_v(0) + I_v(0) = p N$ and all four
classes nonnegative at time $0$. If the [vaccinated reproduction number](rv.md)
$R_v = (\beta / \gamma)(1 - \varepsilon p)$ equals $1$, then for every $t \ge 0$

$$
I(t) \le \frac{I(0)}{1 + c\, I(0)\, t}, \qquad
I = I_u + I_v, \quad c = \frac{\beta (1 - \varepsilon)}{N},
$$

where the denominator is positive. For $c\, I(0) > 0$ the total infected decays at least like
$1 / t$.
