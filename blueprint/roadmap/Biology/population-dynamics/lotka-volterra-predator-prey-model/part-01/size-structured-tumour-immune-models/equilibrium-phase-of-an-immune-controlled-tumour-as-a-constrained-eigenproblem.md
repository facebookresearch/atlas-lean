# Equilibrium phase of an immune-controlled tumour as a constrained eigenproblem

Let $n(t, z)$ be the size density of tumour cells ($z \ge 0$), $c(t, x)$ the concentration of activated immune cells and $\phi(t, x)$ a chemoattractant on a bounded domain $\Omega$, with tumour mass $\mu_1(t) = \int_0^\infty z\,n(t, z)\,dz$ and immune killing rate $\bar\mu_c(t) = \int_\Omega \delta(x)c(t, x)\,dx$ for a weight $\delta \ge 0$:

$$\begin{aligned}
\partial_t n + \partial_z(Vn) &= Q(n) - \bar\mu_c\,n, \\
\partial_t c + \nabla_x\cdot\bigl(c\,\chi\nabla_x\phi - D\nabla_x c\bigr) &= \mu_1 R - \gamma c, \\
-K\Delta_x\phi &= \mu_1\Bigl(\sigma(x) - \tfrac{1}{|\Omega|}\textstyle\int_\Omega\sigma\Bigr),
\end{aligned}$$

with $n(t, 0) = 0$, $c = 0$ on $\partial\Omega$ and $K\nabla_x\phi\cdot\nu = 0$ on $\partial\Omega$. Here $V > 0$ is the growth rate, $Q$ a growth–division (cell-division) operator, $R \ge 0$ the activation source of immune cells, $\gamma$ their death rate, $\chi$ the chemotactic sensitivity and $D$ the diffusion coefficient.

Without immune cells the growth–division equation has a Perron eigenpair $(\lambda, \bar N)$: $\partial_z(V\bar N) - Q(\bar N) + \lambda\bar N = 0$, $\bar N(0) = 0$, $\bar N > 0$, $\int\bar N = 1$, $\lambda > 0$, and $n(t, z) \sim \mu_0 e^{\lambda t}\bar N(z)$. An equilibrium (immune-controlled) state is $n = \mu_0\bar N$ with mass $\mu_1 = \mu_0\int_0^\infty z\bar N\,dz$, together with $C$ solving

$$\gamma C - \nabla_x\cdot(D\nabla_x C) + \mu_1\nabla_x\cdot(\chi C\nabla_x\Phi) = \mu_1 R, \qquad C|_{\partial\Omega} = 0,$$

where $-K\Delta_x\Phi = \sigma - |\Omega|^{-1}\int_\Omega\sigma$ with homogeneous Neumann data, subject to the constraint

$$\int_\Omega \delta(x)\,C(x)\,dx = \lambda .$$

If $R \in L^2(\Omega)$ is nonnegative, $R \not\equiv 0$, $\delta \not\equiv 0$ and $\lambda > 0$ is small enough, there is a unique mass $\mu_1(\lambda) > 0$ for which the solution $C_{\mu_1}$ of the stationary problem satisfies the constraint; it is the residual tumour mass of the equilibrium phase. The source's Theorem 2.1 assumes only $R \ge 0$ and $\delta \ge 0$; the page adds $R \not\equiv 0$ and $\delta \not\equiv 0$, the nondegeneracy that the theorem's implicit-function argument needs (a positive derivative of $\mu_1 \mapsto \int\delta C_{\mu_1}$ at $0$): if $R \equiv 0$ or $\delta \equiv 0$, then $\int_\Omega\delta C_{\mu_1} = 0 \ne \lambda$ for every $\mu_1$.

## Expansion

At equilibrium the immune death rate must exactly cancel the intrinsic exponential growth rate $\lambda$ of the tumour, so the size profile is the immune-free eigenfunction and the mass $\mu_1$ is fixed implicitly by the stationary immune problem; the smallness condition makes the map $\mu_1 \mapsto \int\delta C_{\mu_1}$ invertible near zero. For constant $V$ and binary division at constant rate $a$, $\lambda = a$, so the condition is a smallness assumption on the division rate. This reduction replaces long simulations of the evolution problem by one eigenproblem and one constrained elliptic solve, which makes the sensitivity of the residual mass to biological and treatment parameters cheap to compute.

## Sources

- K. Atsou, S. Khou, F. Anjuère, V. M. Braud and T. Goudon, "Analysis of the equilibrium phase in immune-controlled tumors provides hints for designing better strategies for cancer treatment", Frontiers in Oncology 12 (2022) 878827, <https://doi.org/10.3389/fonc.2022.878827>, PMCID PMC9271975. System (1a)–(1e), Section 2.1.1, Equations (5)–(8) and Theorem 2.1.
