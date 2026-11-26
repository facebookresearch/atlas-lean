# Lipschitz stability of proliferation and competition coefficients from two snapshots

**Model.** On a bounded smooth domain $\Omega$ (for example the brain) and $Q=\Omega\times(0,T)$, the tumor cell density $\rho$ solves

$$
\begin{cases}
\partial_t\rho-\nabla\cdot\bigl(\gamma(\rho)\nabla\rho\bigr)+\rho\,\bigl(\mu(x)-\xi(x)\rho\bigr)=0 & \text{in } Q,\\
\rho=b & \text{on } \partial\Omega\times(0,T),\\
\rho(\cdot,0)=\rho_0 & \text{in } \Omega,
\end{cases}
$$

with density-dependent diffusion $0<\underline\alpha\le\gamma(\rho)\le\overline\alpha$, spatially varying proliferation coefficient $\mu$ and competition (saturation) coefficient $\xi$ (reaction term written as in the source, $f(x,\rho)=\mu\rho-\xi\rho^2$), and boundary data $b>b_0>0$. The admissible set $\mathcal U$ consists of triples $(\mu,\xi,\rho_0)\in C^{2+\alpha}\times C^{2+\alpha}\times C^{4+\alpha}(\bar\Omega)$ with norms at most $M$, $\mu,\xi>r_0$, $\rho_0\ge r_0>0$ and the first-order compatibility conditions at $\partial\Omega$. For each element of $\mathcal U$ the problem has a solution in $C^{4+\alpha,2+\alpha/2}(\bar Q)$ bounded in terms of $M$.

**Data.** For $0<t_0<t_1<T$ and a subdomain $\omega\subset\Omega$: two full snapshots $\rho(\cdot,t_0)$, $\rho(\cdot,t_1)$ on $\Omega$ and the time trace $\rho|_{\omega\times(0,T)}$.

**Theorem (uniqueness and stability).** Let $\rho,\tilde\rho$ be the solutions for $(\mu,\xi,\rho_0),(\tilde\mu,\tilde\xi,\tilde\rho_0)\in\mathcal U$ with the same boundary data, and set

$$
G=\|\rho-\tilde\rho\|^2_{H^2(0,T;L^2(\omega))}+\|(\rho-\tilde\rho)(\cdot,t_0)\|^2_{H^2(\Omega)}+\|(\rho-\tilde\rho)(\cdot,t_1)\|^2_{H^2(\Omega)} .
$$

There is a constant $C$ (depending on $\Omega,\omega,T,t_0,t_1,M,r_0$ and $\gamma$) such that

$$
\|\mu-\tilde\mu\|^2_{L^2(\Omega)}+\|\xi-\tilde\xi\|^2_{L^2(\Omega)}\le C\,G,\qquad \|\rho_0-\tilde\rho_0\|_{L^2(\Omega)}\le C\,\bigl|\log G\bigr|^{-1}.
$$

In particular the data determine $(\mu,\xi,\rho_0)$ uniquely: Lipschitz-stably for the reaction coefficients, only logarithmically for the initial condition (a backward parabolic problem).

## Expansion

The difference $y=\rho-\tilde\rho$ solves a linear parabolic equation whose source contains $(\mu-\tilde\mu)\tilde\rho$ and $(\xi-\tilde\xi)\tilde\rho^2$. Because the two unknown coefficients multiply the independent functions $\tilde\rho$ and $\tilde\rho^2$, evaluating the equation and its time derivative at the two snapshot times gives a $2\times2$ system that can be solved for $\mu-\tilde\mu$ and $\xi-\tilde\xi$ when $\tilde\rho(\cdot,t_0)$ and $\tilde\rho(\cdot,t_1)$ differ (which the positivity bounds guarantee). Time derivatives of $y$ at $t_0,t_1$ are controlled by local Carleman estimates on $(t_i-\delta,t_i+\delta)$ with observation in $\omega$, in the Bukhgeim–Klibanov style, absorbing the coefficient terms for large Carleman parameter. The initial condition is then recovered by backward uniqueness for the linear equation, whose conditional stability is logarithmic. Numerically, a two-stage algorithm shifts the time origin to $t_0$ to first fit $\mu,\xi$ without knowing $\rho_0$, then reconstructs $\rho_0$.

## Sources

- B. Chen and K. Ren, "Recovering the initial condition and physical coefficients in a nonlinear PDE model of cell invasion", arXiv:2606.11554 (2026), Section 1 (model and data), Section 2 (forward well-posedness theorem) and Section 3 (stability theorem with estimates for $\mu,\xi$ and $\rho_0$; Carleman lemmas), <https://doi.org/10.48550/arXiv.2606.11554>.
