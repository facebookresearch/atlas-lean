# Sodium activation opening rate α_m

The opening rate of the sodium activation gate $m$, in 1/ms, as a function of the membrane
depolarization $V$ from rest, in mV:

$$\alpha_m(V) = \frac{0.1\,(25 - V)}{e^{(25 - V)/10} - 1} \quad (V \ne 25),
\qquad \alpha_m(25) = 1,$$

the value at $V = 25$ being the limit of the formula there. Equivalently
$\alpha_m(V) = \varphi((25 - V)/10)$ for every real $V$, where $\varphi$ is the
[extension of $x/(e^x - 1)$ by $1$ at $0$](vtrap.md). The rate is [positive](alpha-m-pos.md) and
[continuously differentiable](cont-diff-alpha-m.md).
