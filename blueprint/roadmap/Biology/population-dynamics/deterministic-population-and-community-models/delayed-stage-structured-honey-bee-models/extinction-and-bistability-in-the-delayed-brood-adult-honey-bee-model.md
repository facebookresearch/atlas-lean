# Extinction and bistability in the delayed brood–adult honey bee model

**Model.** Let $B(t)$ and $H(t)$ be the brood and adult bee populations of a hive. The queen lays eggs at rate $r$; brood survival is cooperative in adult care and regulated by brood load, $H^2/(K+H^2+\alpha B)$ with $K>0$, $\alpha\ge 0$; brood and adults die at constant rates $d_b,d_h>0$; and brood matures after a fixed time $\tau>0$ with survival $e^{-d_b\tau}$. Writing $\Phi(t)=\dfrac{rH(t)^2}{K+H(t)^2+\alpha B(t)}$ for recruitment of new brood,

$$B'=\Phi(t)-d_bB-e^{-d_b\tau}\Phi(t-\tau),\qquad H'=e^{-d_b\tau}\Phi(t-\tau)-d_hH ,$$

with nonnegative continuous history on $[-\tau,0]$ and the compatible brood condition $B(0)=\int_{-\tau}^0\Phi(s)e^{d_bs}\,ds$ (brood alive at time $0$ is exactly the surviving cohorts laid in the last $\tau$ days).

**Results.**

*(1)* The model is positively invariant and bounded on $C([-\tau,0],\mathbb R_+)^2$.

*(2)* The extinction equilibrium $E_e=(0,0)$ is always locally asymptotically stable (cooperative brood care gives a strong Allee effect). If $d_h>\dfrac{re^{-d_b\tau}}{2\sqrt K}$, $E_e$ is globally stable.

*(3)* Interior equilibria satisfy $B^\ast=\dfrac{d_h(e^{d_b\tau}-1)}{d_b}H^\ast$. Let

$$\Theta=\frac{d_br-\alpha d_h^2e^{d_b\tau}(e^{d_b\tau}-1)}{2d_hd_be^{d_b\tau}\sqrt K}.$$

If $\Theta>1$ there are exactly two interior equilibria $H_1^\ast<H_2^\ast$, the roots of $d_b(K+H^2)d_h+\alpha d_h^2(e^{d_b\tau}-1)H=e^{-d_b\tau}rd_bH$; if $\Theta=1$ they merge. $H_1^\ast$ increases and $H_2^\ast$ decreases in $\alpha$, $K$, $d_b$ and $d_h$, and the reverse holds in $r$.

*(4)* For $\alpha=0$ and $r>2d_he^{d_b\tau}\sqrt K$, $E_1$ is unstable and $E_2$ is locally asymptotically stable for every maturation delay $\tau$; at the critical value $d_h=re^{-d_b\tau}/(2\sqrt K)$ the unique interior equilibrium $\big(r(1-e^{-d_b\tau})/(2d_b),\sqrt K\big)$ is locally asymptotically stable for every $\tau>0$.

So with $\alpha=0$ the colony is bistable between collapse and the large equilibrium $E_2$ when $r\ge 2d_he^{d_b\tau}\sqrt K$, and collapses from every initial state when $r<2d_he^{d_b\tau}\sqrt K$; the delay affects only the location of the equilibria, not their stability.

## Expansion

At equilibrium, the brood equation balances recruitment against brood death and maturation, giving the fixed brood-to-adult ratio, while the adult equation reduces to a quadratic in $H$ whose discriminant condition is $\Theta>1$. The per-capita adult recruitment $e^{-d_b\tau}rH/(K+H^2)$ is maximized at $H=\sqrt K$ with value $re^{-d_b\tau}/(2\sqrt K)$, which explains the global extinction threshold. With $\alpha=0$ the adult equation decouples into the scalar delay equation $H'=e^{-d_b\tau}f(H(t-\tau))-d_hH$ with $f$ increasing, so brood is slaved to the adult history; the linearization at $E_i$ is $\lambda+d_h=e^{-d_b\tau}f'(H_i^\ast)e^{-\lambda\tau}$, and the sign of $e^{-d_b\tau}f'(H_i^\ast)-d_h$ (positive at $E_1$, negative at $E_2$) decides stability for every $\tau$. The degenerate critical case uses a center-manifold normal form.

## Sources

- Jun Chen, Komi Messan, Marisabel Rodriguez Messan, Gloria DeGrandi-Hoffman, Dingyong Bai and Yun Kang, "How to model honeybee population dynamics: stage structure and seasonality", arXiv:2003.09796 (2020), Theorems 3.1–3.4 and Proposition 3.1, <https://doi.org/10.48550/arXiv.2003.09796>.
