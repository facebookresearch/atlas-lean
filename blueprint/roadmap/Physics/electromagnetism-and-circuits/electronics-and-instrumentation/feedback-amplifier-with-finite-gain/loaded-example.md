# Example: halved dividers, $A_0 = 10$, $\beta = 1$, $\omega_p = 2$

With equal source and input resistances $R_s = R_{in} = 1$ and equal output and load resistances
$R_o = R_L = 1$, the [source divider](source-divider.md) and the [load divider](load-divider.md) are
both $1/2$. With open-loop DC gain $A_0 = 10$, feedback factor $\beta = 1$, pole frequency
$\omega_p = 2$ and dividers $a = b = 1/2$, the [loaded closed-loop transfer](loaded-transfer.md) at
$s = 0$ is

$$G(0) = \frac{\frac12 \cdot \frac12 \cdot 10}{1 + 1 \cdot \frac12 \cdot 10} = \frac{5}{12},$$

and the [closed-loop pole location](closed-loop-pole.md) is
$-2\,(1 + 1 \cdot \frac12 \cdot 10) = -12$.
