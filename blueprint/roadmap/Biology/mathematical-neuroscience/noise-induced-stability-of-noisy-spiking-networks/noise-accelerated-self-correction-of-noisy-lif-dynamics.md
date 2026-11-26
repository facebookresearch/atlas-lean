# Noise-accelerated self-correction of noisy leaky integrate-and-fire dynamics

Model the subthreshold membrane potentials $u_t \in \mathbb{R}^d$ of a layer of noisy LIF neurons by the Itô SDE

$$du_t = f(u_t, I_t)\,dt + g(u_t, I_t)\,dW_t, \qquad f(u, I) = a_1 u + B_1 I, \qquad g(u, I) = a_2\,\mathrm{diag}(\mathbf 1) + b_2\, f(u, I),$$

with $a_1 \in \mathbb{R}$, $a_2, b_2 \ge 0$, $B_1 \in \mathbb{R}^{d \times d}$ and $W$ a $d$-dimensional Wiener process. A layer of noisy LIF neurons with membrane time constant $\tau_m$ and additive noise amplitude $\sigma$ is the case $a_1 = -1/\tau_m$, $a_2 = \sigma$, $b_2 = 0$. Run two copies from $u_0$ and $u_0 + \epsilon_0$ with the same input and the same Wiener path, and let $\epsilon_t$ be their difference, with increments $\Delta f(\epsilon_t)$ and $\Delta g(\epsilon_t)$. The trivial solution $\epsilon \equiv 0$ is almost surely exponentially stable if the sample Lyapunov exponent

$$L_E = \limsup_{t \to \infty} \frac1t \log \|\epsilon_t\|$$

is almost surely negative for every $\epsilon_0$.

Suppose $a_2\|\epsilon\| \le \|\Delta g(\epsilon)\|_F \le (a_2 + b_2)\|\epsilon\|$ for all nonzero $\epsilon$. Then, almost surely and for every $\epsilon_0$,

$$a_1 - \tfrac12 a_2^2 - b_2^2 - 2a_2 b_2 \;\le\; L_E \;\le\; a_1 - \tfrac12 a_2^2 + \tfrac12 b_2^2 + a_2 b_2 .$$

In particular, for purely additive noise ($b_2 = 0$) the upper bound is $a_1 - \frac12 a_2^2$, strictly below the noise-free exponent $a_1 = -1/\tau_m$: membrane noise makes small perturbations of the subthreshold state die out faster.

## Depends on

- [Period of the leaky integrate-and-fire neuron](../leaky-integrate-and-fire-neuron/lif-period.md)

## Expansion

Apply the stochastic Lyapunov theorem with $V(\epsilon) = \|\epsilon\|^2$: if $c_2 V \le \mathcal L V \le C_2 V$ and $c_3 V^2 \le \|V_\epsilon \Delta g\|_F^2 \le C_3 V^2$, then $\frac{c_2}{2} - \frac{C_3}{4} \le L_E \le \frac{C_2}{2} - \frac{c_3}{4}$ almost surely. For the linear drift, $\mathcal L V$ lies between $(2a_1 + a_2^2)V$ and $(2a_1 + (a_2+b_2)^2)V$, and $\|V_\epsilon \Delta g\|_F^2$ between $4a_2^2 V^2$ and $4(a_2+b_2)^2 V^2$; substituting gives the two bounds. The mechanism is the Itô correction: the diffusion term contributes $-\frac12 a_2^2$ to the growth rate of $\log\|\epsilon_t\|$, so noise stabilizes the trivial solution even though it adds variance to each trajectory. In the source the neurons fire by escape noise, $o_t \sim \mathrm{Bernoulli}(F_\epsilon(u_t - v_{th}))$ with $F_\epsilon$ the noise distribution function, and this stability result is Theorem 1 of its analysis section.

## Sources

- G. Ma, R. Yan, H. Tang, Exploiting noise as a resource for computation and learning in spiking neural networks, Patterns 4 (2023), 100831, Eqs. (5)–(9), (20)–(24), Theorem 1. <https://doi.org/10.1016/j.patter.2023.100831> (PMCID: PMC10591140)
- X. Mao, Stochastic Differential Equations and Applications, 2nd ed., Horwood, 2007, Chapter 4 (almost sure exponential stability).
