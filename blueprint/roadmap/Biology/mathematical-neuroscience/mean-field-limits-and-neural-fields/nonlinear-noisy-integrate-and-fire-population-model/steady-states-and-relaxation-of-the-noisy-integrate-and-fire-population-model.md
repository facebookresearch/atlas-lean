# Steady states and relaxation of the noisy integrate-and-fire population model

**Setting.** Take the NNLIF Fokker–Planck model of [finite-time blow-up of excitatory noisy integrate-and-fire networks](finite-time-blow-up-of-excitatory-noisy-integrate-and-fire-networks.md) with drift $h(v,N) = bN - v$, threshold $V_F$ and reset $V_R < V_F$. Steady states are pairs $(p_\infty, N_\infty)$ solving the stationary problem; they correspond to fixed points $N = 1/I(N)$ of an explicit integral $I(N) > 0$ (the normalization of the stationary profile), which satisfies $I(0) \le \sqrt{2\pi}\,\frac{V_F - V_R}{\sqrt{a_0}}\exp\!\big(\frac{\max(V_R^2, V_F^2)}{2a_0}\big)$.

**Theorem (constant noise $a(N) = a_0$).**
1. For $b < 0$, and for $b > 0$ small enough, there is a unique steady state.
2. If $0 < b < V_F - V_R$, or if $0 < 2a_0 b < (V_F - V_R)^2 V_R$, there is at least one steady state.
3. If $2a_0 b < (V_F - V_R)^2 V_R$ and $b > V_F - V_R$, there are at least two steady states.
4. If $b > \max\big(2(V_F - V_R),\ 2V_F I(0)\big)$ (high connectivity), there is no steady state.

**Corollary (linear noise $a(N) = a_0 + a_1 N$, $a_0, a_1 > 0$).**
1. If $b < V_F - V_R$, or if $b > 0$ and $2a_0 b + 2a_1 V_R < (V_F - V_R)^2 V_R$, there is at least one steady state.
2. If $2a_0 b + 2a_1 V_R < (V_F - V_R)^2 V_R$ and $b > V_F - V_R$, there are at least two steady states.
3. If $b > \max\big(2(V_F - V_R),\ 2V_F I(0)\big)$, there is no steady state.

No uniqueness is claimed for linear noise: the source notes that the number of steady states is hard to settle here, and that for $b < 0$ the function $I(N)$ may have a minimum.

**Relaxation in the linear case.** For $b = 0$ and $a = a_0$, fast-decaying solutions satisfy, for every smooth convex $G$, a relative-entropy dissipation identity, and there is $\nu > 0$ (a Poincaré constant for the weight $p_\infty$) such that

$$\int_{-\infty}^{V_F} p_\infty \Big(\frac{p(v,t) - p_\infty(v)}{p_\infty(v)}\Big)^2 dv \le e^{-2a_0\nu t}\int_{-\infty}^{V_F} p_\infty \Big(\frac{p^0(v) - p_\infty(v)}{p_\infty(v)}\Big)^2 dv.$$

## Depends on

- [Finite-time blow-up of excitatory noisy integrate-and-fire networks](finite-time-blow-up-of-excitatory-noisy-integrate-and-fire-networks.md)

## Proof sketch

For fixed $N$ the stationary equation is linear and solvable in closed form: the flux is constant $N$ on $(V_R, V_F)$ and zero below $V_R$, which gives $p_\infty$ as $N$ times an explicit Gaussian integral, and mass one becomes $N\,I(N) = 1$. For $b < 0$ the map $N \mapsto N I(N)$ is increasing, giving uniqueness. For $b > 0$, $I$ is decreasing and convex with $I(N) \to 0$, so $N I(N)$ can cross $1$ zero, one or two times depending on the size of $b$, producing the existence, multiplicity and non-existence regimes. In the linear case the general relative entropy inequality, with $G(x) = (x-1)^2$ and the Poincaré inequality, yields exponential convergence. Together with blow-up, these results show how the balance between noise $a_0$ and connectivity $b$ controls the network state.

## Sources

- María J. Cáceres, José A. Carrillo and Benoît Perthame, "Analysis of Nonlinear Noisy Integrate&Fire Neuron Models: blow-up and steady states", *The Journal of Mathematical Neuroscience* 1 (2011), 7, <https://doi.org/10.1186/2190-8567-1-7>. Preprint version: arXiv:1010.4683 (2010), Theorem 3.1 and Corollary 3.5 (Section 3), Theorem 4.1, Proposition 4.2 and Corollary 4.3 (Section 4), <https://doi.org/10.48550/arXiv.1010.4683>.
