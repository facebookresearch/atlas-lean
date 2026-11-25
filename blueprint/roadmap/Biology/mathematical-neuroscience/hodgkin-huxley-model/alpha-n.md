# Potassium activation opening rate α_n

The opening rate of the potassium activation gate $n$, in 1/ms, as a function of the membrane
depolarization $V$ from rest, in mV:

$$\alpha_n(V) = \frac{0.01\,(10 - V)}{e^{(10 - V)/10} - 1} \quad (V \ne 10),
\qquad \alpha_n(10) = 0.1,$$

the value at $V = 10$ being the limit of the formula there. Equivalently
$\alpha_n(V) = \varphi((10 - V)/10)/10$ for every real $V$, where $\varphi$ is the
[extension of $x/(e^x - 1)$ by $1$ at $0$](vtrap.md).
