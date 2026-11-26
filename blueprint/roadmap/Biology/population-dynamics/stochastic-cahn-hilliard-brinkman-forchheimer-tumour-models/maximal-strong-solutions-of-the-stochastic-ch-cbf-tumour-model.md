# Maximal strong solutions of the stochastic Cahn–Hilliard–convective Brinkman–Forchheimer tumour model

Let $\mathcal{O}\subset\mathbb{R}^d$, $d\in\{2,3\}$, be a bounded domain with smooth boundary. A two-phase (tumour/healthy) tissue is described by the volume-averaged mixture velocity $v$ (divergence free), pressure $p$, phase field $\phi$ (with pure phases near $\phi=\pm1$), chemical potential $\mu$ and nutrient concentration $\sigma$. The stochastic Cahn–Hilliard–convective Brinkman–Forchheimer (CH-CBF) tumour model is

$$dv+\big[(v\cdot\nabla)v+\eta|v|^{r-1}v-\nu\Delta v+\nabla p-\mu\nabla\phi-z\big]\,dt=G_1(v)\,dW_1,\qquad \nabla\cdot v=0,$$

$$d\phi+\big[(v\cdot\nabla)\phi-\Delta\mu-(P\sigma-A-\alpha u)\,h(\phi)\big]\,dt=0,\qquad \mu=-\epsilon\Delta\phi+\epsilon^{-1}\psi'(\phi),$$

$$d\sigma+\big[(v\cdot\nabla)\sigma-\Delta\sigma+c\,\sigma h(\phi)+b(\sigma-w)\big]\,dt=G_2(\sigma)\,dW_2,$$

with $v=0$ and $\partial_n\mu=\partial_n\phi=\partial_n\sigma=0$ on $\partial\mathcal{O}$. Here $\eta,\nu,\epsilon,P,A,\alpha,c,b>0$ are the Forchheimer coefficient, viscosity, interface width, proliferation, apoptosis, drug effectiveness, nutrient consumption and supply rates; $r\ge1$ is the damping exponent; $W_1,W_2$ are independent cylindrical Wiener processes; $z$, $u\in[0,1]$ (a drug concentration) and $w$ are predictable sources with $(z,u,w)\in L^2(\Omega;L^2_{\rm loc}([0,\infty);\mathcal{H}))$, where $\mathcal{H}=L^2_{\rm div}\times H^1\times L^2$.

**Hypotheses.** (i) $h:\mathbb{R}\to[0,1]$ is $C^1$ with bounded derivative. (ii) $\psi\in C^4$ is non-negative and splits as $\psi=\psi_1+\psi_2$ with $R_1(1+|s|^{\rho-2})\le\psi_1''(s)\le R_2(1+|s|^{\rho-2})$, $|\psi_2''|\le R_3$, $\rho\in[2,6]$, together with polynomial bounds $|\psi^{(k)}(s)|\le C(1+|s|^{6-k})$ for $k=2,3,4$ (the double well $\tfrac14(s^2-1)^2$ qualifies). (iii) $G_1,G_2$ are uniformly Lipschitz with linear growth as Hilbert–Schmidt-valued maps on each of the levels $L^2$, $H^1$ and $H^2$ (respectively $L^2_{\rm div}$, $V$, $D(A_0)$ for $G_1$, with $V$ the divergence-free $H^1_0$ fields and $A_0$ the Stokes operator). (iv) The initial data satisfy $(v_0,\phi_0,\sigma_0)\in L^2(\Omega;\mathcal{V})$, $\mathcal{V}=V\times H^2\times H^1$.

**Statement.** Assume $r\ge1$ if $d=2$ and $r\in[1,3]$ if $d=3$.

1. *Local strong solutions.* There is an a.s. strictly positive stopping time $\tau$ and a solution with $(v,\phi,\sigma)(\cdot\wedge\tau)\in L^2(\Omega;C([0,\infty);\mathcal{V}))$ and $(v,\phi,\sigma)\mathbf{1}_{t\le\tau}\in L^2(\Omega;L^2_{\rm loc}([0,\infty);D(A_0)\times H^4\times H^2))$.
2. *Weak–strong uniqueness.* A local strong solution and a local weak solution starting from the same data coincide pathwise up to the smaller of their stopping times.
3. *Maximal solution and blow-up alternative.* There is a unique maximal strong solution $\{(v,\phi,\sigma),\{t_R\}_{R\in\mathbb{N}},\xi\}$: stopping times $t_R\uparrow\xi$ such that each $\{(v,\phi,\sigma),t_R\}$ is a local strong solution, and on $\{\xi<\infty\}$

$$\sup_{t\in[0,\xi)}\|(v,\phi,\sigma)(t)\|_{\mathcal{V}}^2+\int_0^{\xi}\big(\|A_0v\|_{L^2}^2+\|\phi\|_{H^4}^2+\|\sigma\|_{H^2}^2\big)\,ds=\infty .$$

Moreover $\{(v,\phi,\sigma);\xi\}$ is a weak solution.

## Expansion

The proof uses a Galerkin scheme with a high–low mode decomposition and the pairwise comparison lemma for stochastic sequences, which yields a.s. convergence in $C([0,\tau];\mathcal{V})$ up to a stopping time. Energy estimates of order $p$ follow from the Ginzburg–Landau energy $\int(\tfrac12|v|^2+\tfrac{\epsilon}{2}|\nabla\phi|^2+\epsilon^{-1}\psi(\phi)+\tfrac12\sigma^2)$. The nutrient advection $(v\cdot\nabla)\sigma$ behaves like the Navier–Stokes nonlinearity and is the reason for the restriction $r\le3$ in three dimensions; in a bounded domain the Forchheimer damping does not supply the extra regularity it gives on the torus, because the Leray projector does not commute with the Laplacian. The maximal time is the essential supremum of existence times of local strong solutions.

## Sources

- K. Rawat and K. Sakthivel, *Strong Solutions for the Stochastic Cahn-Hilliard Convective Brinkman-Forchheimer Model for Tumor Growth*, arXiv:2605.29779 (2026), <https://doi.org/10.48550/arXiv.2605.29779>. Assumptions [A1]–[A5] (Section 3); Proposition 4.1 (weak–strong uniqueness); Proposition 4.3 (local strong solution); Theorem 4.1 (maximal solution).
