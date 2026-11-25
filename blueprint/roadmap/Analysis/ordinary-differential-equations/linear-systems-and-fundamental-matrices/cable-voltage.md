# Transfer-form voltage of a uniform cable

For real numbers $r_m$, $r_i$, $V_0$, $I_0$ and $x$, the transfer-form steady-state voltage is

$$V(x)=V_0\cosh(x/\lambda)-r_\infty I_0\sinh(x/\lambda),$$

where $\lambda=\sqrt{r_m/r_i}$ is the [length constant](length-constant.md) and
$r_\infty=\sqrt{r_m r_i}$ the [characteristic resistance](char-resistance.md); $V(0)=V_0$. For
$r_m,r_i>0$, together with the [transfer-form current](cable-current.md) it is a
[steady state on every set of positions](is-steady-state-cable.md), with inlet voltage $V_0$ and
inlet current $I_0$ at $x=0$. The formula is defined for all real inputs: with the convention
$u/0=0$, $V(x)=V_0$ for every $x$ when $\lambda=0$.
