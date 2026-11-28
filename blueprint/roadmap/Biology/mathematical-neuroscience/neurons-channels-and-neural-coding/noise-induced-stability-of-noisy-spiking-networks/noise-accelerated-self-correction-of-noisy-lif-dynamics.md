# Lyapunov-exponent bounds for noisy leaky integrate-and-fire dynamics

Model the subthreshold membrane potentials $u_t \in \mathbb{R}^d$ of a layer of noisy LIF neurons by the Itô SDE

$$du_t = f(u_t, I_t)\,dt + g(u_t, I_t)\,dW_t, \qquad f(u, I) = a_1 u + B_1 I, \qquad g(u, I) = a_2\,\mathrm{diag}(\mathbf 1) + b_2\, \mathrm{diag}\big(f(u, I)\big),$$

with $a_1 \in \mathbb{R}$, $a_2, b_2 \ge 0$, $B_1 \in \mathbb{R}^{d \times d}$ and $W$ a $d$-dimensional Wiener process. A layer of noisy LIF neurons with membrane time constant $\tau_m$ and additive noise amplitude $\sigma$ is the case $a_1 = -1/\tau_m$, $a_2 = \sigma$, $b_2 = 0$. Run two copies from $u_0$ and $u_0 + \epsilon_0$ with the same input and the same Wiener path, and let $\epsilon_t$ be their difference, with increments $\Delta f(\epsilon_t)$ and $\Delta g(\epsilon_t)$. The trivial solution $\epsilon \equiv 0$ is almost surely exponentially stable if the sample Lyapunov exponent

$$L_E = \limsup_{t \to \infty} \frac1t \log \|\epsilon_t\|$$

is almost surely negative for every $\epsilon_0$.

Suppose $a_2\|\epsilon\| \le \|\Delta g(\epsilon)\|_F \le (a_2 + b_2)\|\epsilon\|$ for all nonzero $\epsilon$. Then, almost surely and for every $\epsilon_0$,

$$a_1 - \tfrac12 a_2^2 - b_2^2 - 2a_2 b_2 \;\le\; L_E \;\le\; a_1 - \tfrac12 a_2^2 + \tfrac12 b_2^2 + a_2 b_2 .$$

For this $g$, $\Delta g(\epsilon) = a_1 b_2\,\mathrm{diag}(\epsilon)$, so $\|\Delta g(\epsilon)\|_F = |a_1| b_2 \|\epsilon\|$ and the hypothesis holds exactly when $a_2 \le b_2|a_1| \le a_2 + b_2$. It fails for the additive-noise LIF case ($b_2 = 0$, $a_2 > 0$): there $\Delta g \equiv 0$, $\epsilon_t = e^{a_1 t}\epsilon_0$ and $L_E = a_1$ exactly, so additive noise with a common Wiener path does not change the exponent.

## Expansion

Apply the stochastic Lyapunov theorem with $V(\epsilon) = \|\epsilon\|^2$: if $c_2 V \le \mathcal L V \le C_2 V$ and $c_3 V^2 \le \|V_\epsilon \Delta g\|_F^2 \le C_3 V^2$, then $\frac{c_2}{2} - \frac{C_3}{4} \le L_E \le \frac{C_2}{2} - \frac{c_3}{4}$ almost surely. For the linear drift, $\mathcal L V$ lies between $(2a_1 + a_2^2)V$ and $(2a_1 + (a_2+b_2)^2)V$, and $\|V_\epsilon \Delta g\|_F^2$ between $4a_2^2 V^2$ and $4(a_2+b_2)^2 V^2$; substituting gives the two bounds. The noise enters these bounds only through $\Delta g$, the part of the diffusion that the two copies feel differently: the Itô correction acts on $\log\|\epsilon_t\|$ only when $\Delta g \ne 0$. With additive noise and a common Wiener path the two copies receive identical kicks, the difference obeys the noise-free equation, and the exponent stays $a_1$; the source reads its additive case as noise-induced stabilization, but that step is not covered by the theorem, whose hypothesis fails there. In the source the neurons fire by escape noise, $o_t \sim \mathrm{Bernoulli}(F_\epsilon(u_t - v_{th}))$ with $F_\epsilon$ the noise distribution function, and this stability result is Theorem 1 of its analysis section.

## Sources

- G. Ma, R. Yan, H. Tang, Exploiting noise as a resource for computation and learning in spiking neural networks, Patterns 4 (2023), 100831, Eqs. (5)–(9), (20)–(24), Theorem 1. <https://doi.org/10.1016/j.patter.2023.100831> (PMCID: PMC10591140)
- X. Mao, Stochastic Differential Equations and Applications, 2nd ed., Horwood, 2007, Chapter 4 (almost sure exponential stability).
