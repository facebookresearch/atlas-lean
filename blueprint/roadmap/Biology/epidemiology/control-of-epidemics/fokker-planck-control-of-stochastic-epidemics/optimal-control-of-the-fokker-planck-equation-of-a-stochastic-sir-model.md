# Optimal control of the Fokker–Planck equation of a stochastic SIR model

**Setting.** A controlled SIR model with birth rate $b$, death rate $\delta$, infection rate $\beta$ and recovery rate $\gamma$ has three time-dependent controls: a reduction $\alpha(t)$ of infectivity (distancing, masks), an extra removal rate $\eta(t)$ of infecteds (treatment or isolation) and a vaccination rate $v(t)$ of susceptibles. With Itô noise and $X=(S,I)$,

$$dS=\big(b-(1-\alpha)\beta SI-(v+\delta)S\big)dt+\sigma_S\,dW_1,\qquad dI=\big((1-\alpha)\beta SI-(\gamma+\eta+\delta)I\big)dt+\sigma_I\,dW_2,$$

with noise intensities $\sigma_S,\sigma_I$ depending on $(S,I)$ and the controls, and with uncertain initial data drawn from a density $f_0$. Writing $dX=F(X,u)dt+\mathrm{diag}(\sigma_1,\sigma_2)\,dW$, the density $f(x,t)$ of $X(t)$ on a bounded positively invariant domain $\Omega\subset\mathbb{R}^2$ solves the Fokker–Planck equation

$$\partial_tf+\nabla\cdot(F(x,u)f)=\tfrac12\sum_{j=1}^2\partial^2_{x_j}\big(\sigma_j^2(x,u)f\big)\quad\text{in }\Omega\times(0,T],\qquad f(\cdot,0)=f_0,$$

with zero-flux boundary conditions. Admissible controls $u=(\alpha,\eta,v)$ take values in a compact box $R_U$ and have components of total variation at most $M$ (allowing bang-bang controls). The cost is

$$J(f,u)=\int_0^T\ell(u(t))\,dt+\int_\Omega K(x)f(x,T)\,dx+\int_0^T\!\!\int_\Omega G(x,t)f(x,t)\,dx\,dt,$$

with intervention cost $\ell$, terminal penalty $K$ and running penalty $G$ (for instance on high prevalence).

**Theorem.**

1. For each bounded control and $f_0\in L^2(\Omega)$ there is a unique weak solution $f\in L^2(0,T;H^1(\Omega))$ with $f_t\in L^2(0,T;H^{-1}(\Omega))$; if $f_0\ge0$ has unit mass, then $f\ge0$ and $\|f(\cdot,t)\|_{L^1}=1$ for all $t$.
2. If $\ell$ is continuous and convex and $\sigma_S^2,\sigma_I^2$ are twice differentiable in $x$ and Lipschitz in $u$ uniformly in $x$, an optimal pair $(f^*,u^*)$ exists.
3. (Pontryagin minimum principle.) For $K\in L^2(\Omega)$, $G\in L^2$, let $q^*$ solve the adjoint equation $-\partial_tq-F\cdot\nabla q=\tfrac12\sum_j\sigma_j^2\partial^2_{x_j}q-G$ with $q(\cdot,T)=-K$. Then for almost every $t$, $u^*(t)$ minimizes over $w\in R_U$ the Hamiltonian

$$H(t,f,q,w)=\ell(w)-\int_\Omega\Big(f\,F(\cdot,w)\cdot\nabla q+\tfrac12\sum_jf\,\sigma_j(\cdot,w)^2\,\partial^2_{x_j}q\Big)dx,$$

evaluated at $f=f^*(\cdot,t)$, $q=q^*(\cdot,t)$.

## Expansion

Controlling the density rather than individual sample paths makes the problem robust to both dynamic noise and uncertain initial data: the costs are expectations under $f$, so the policy is optimal on average over the possible epidemics. Existence follows from compactness of the admissible set (Helly's selection theorem gives pointwise a.e. convergent subsequences of bounded-variation controls), uniform parabolic energy bounds on $f$, continuity of the control-to-state map, and weak lower semicontinuity of the convex cost. The adjoint equation is the backward Kolmogorov equation with source $-G$, and the minimum principle follows from needle variations of the control, using that $J$ is linear in $f$.

## Sources

- Christian Parkinson, Souvik Roy, "A Fokker-Planck Framework for Control of Epidemics", arXiv:2601.20181 (2026): Section 2 (controlled SIR model, stochastic system, Fokker–Planck equation, existence proposition, admissible controls and cost functional), Section 3 (existence of an optimal control theorem, adjoint existence proposition, Pontryagin minimum principle theorem and the optimality system corollary). <https://doi.org/10.48550/arXiv.2601.20181> Published version: Journal of Mathematical Biology 93 (2026) 47, <https://doi.org/10.1007/s00285-026-02462-7>.
