# Well-posedness and finite-time breakdown for Euler-alignment systems with diffusive chemotaxis

**Model.** A population with density $\rho(x,t)$ and velocity $u(x,t)$ on $\mathbb R^n$ aligns velocities through a Cucker–Smale-type communication kernel and is attracted up the gradient of a self-produced diffusing chemical $f$:
$$\begin{cases}
\partial_t\rho+\nabla\cdot(\rho u)=0,\\[2pt]
\partial_tu+(u\cdot\nabla)u=\displaystyle\int_{\mathbb R^n}\phi(|x-y|)\big(u(y,t)-u(x,t)\big)\rho(y,t)\,dy+\gamma\nabla f,\\[2pt]
\partial_tf-\operatorname{tr}\big(a(x,t)\nabla^2f\big)+b\cdot\nabla f=\psi*\rho,
\end{cases}$$
with chemotactic strength $\gamma>0$ and $a=\sigma\sigma^{\mathsf T}$. Assume (H1) $\rho_0\in L^1_+\cap L^\infty$, $u_0\in W^{1,\infty}$, $f_0\in W^{1,\infty}$; (H2) a radial communication kernel given by a nonnegative $\phi\in W^{1,\infty}([0,\infty))$; (H3) a production kernel $\psi\in W^{1,\infty}$; (C1) $a$ and $b$ bounded and parabolically Hölder continuous; and (C2) $a$ uniformly elliptic.

**Theorem.**

1. (Local well-posedness) There is $T_*>0$, depending on $n$, $\gamma$, the structural constants, $\|\rho_0\|_{L^1}$, $\|\rho_0\|_{L^\infty}$, $\|u_0\|_{W^{1,\infty}}$ and $\|\nabla f_0\|_{L^\infty}$, such that a unique strong solution exists on $[0,T_*]$ with $\rho\in C([0,T_*];L^1_+)\cap L^\infty(0,T_*;L^\infty)$. No spatial derivative of $\rho_0$ is required.
2. (Continuation) Writing $m_0=\|\rho_0\|_{L^1}$, along the maximal solution

$$\sup_{t\le\tau}\|u(t)\|_{L^\infty}\le e^{2\|\phi\|_\infty m_0\tau}\Big[\|u_0\|_{L^\infty}+\gamma C_T\tau\|\nabla f_0\|_{L^\infty}+\tfrac{2\gamma}{3}C_T\|\psi\|_\infty m_0\tau^{3/2}\Big],$$

so $u$ itself never blows up. The solution extends past $T_{\max}<T$ as long as $\sup_{t<T_{\max}}\|\nabla u(t)\|_{L^\infty}<\infty$; breakdown means that $\nabla u$ blows up.
3. (Finite-time breakdown) Fix a characteristic $X(\cdot;a)$ along which a certain auxiliary quantity $\mathcal S(t)$ built from the solution stays nonnegative. If the initial compression $-\nabla\cdot u_0(a)$ exceeds an explicit threshold depending on $\gamma$, the kernels and the data (and a compatibility condition on the time scales holds), then $T_{\max}$ is finite, with an explicit upper bound.
4. (One dimension) Let $Z_0=\|(\partial_xu_0)^-\|_\infty$ and let $A^\gamma_\tau$ bound the time integral of the chemotactic forcing along characteristics. If $e^{B\tau}\tau(Z_0+A^\gamma_\tau)<1$, then the solution exists on $[0,\tau]$ and $\partial_xu$ stays bounded there.

## Expansion

Along characteristics the divergence $d=\nabla\cdot u$ satisfies a Riccati-type inequality $d'\le-\frac{d^2}{n}-(\text{alignment damping})\,d+\gamma\,\Delta f$. Alignment acts like a damping term, while the chemotactic source $\gamma\Delta f$, controlled by parabolic estimates on the fundamental solution of the $f$-equation, can drive compression. Sufficiently compressive initial data then reach $d=-\infty$ in finite time. In one dimension the critical-threshold analysis of one-dimensional Euler-alignment systems is perturbed by the chemotactic forcing: the subcritical region shrinks as $\gamma$ grows, and numerical simulations show the transition from regular to singular regimes as the chemotactic strength increases. Bounding $u$ uniformly requires only the $L^1$ mass, because both alignment and chemotaxis are controlled through $\rho$ in convolution form.

## Sources

- Marta Menci, Marco Papi, "Well-posedness and finite-time breakdown for Euler-alignment systems with diffusive chemotaxis", arXiv:2611.27940 (2026), Section 2 (model, hypotheses (H1)–(H3), (C1)–(C2)), Theorems 1–4 and Proposition 1, <https://doi.org/10.48550/arXiv.2611.27940>.
