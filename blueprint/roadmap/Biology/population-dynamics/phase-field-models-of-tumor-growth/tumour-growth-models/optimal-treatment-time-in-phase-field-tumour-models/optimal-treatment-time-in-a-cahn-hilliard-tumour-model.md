# Optimal treatment time in a Cahn–Hilliard tumour model

**State equations.** In a bounded domain $\Omega \subset \mathbb{R}^3$ with $C^3$ boundary, let $\varphi$ be the tumour/healthy-tissue phase field (the value $\varphi = 1$ means tumour and $\varphi = -1$ healthy tissue; $\varphi$ is not assumed to stay in $[-1,1]$), $\mu$ its chemical potential, $\sigma$ the nutrient concentration, and $u \in [0,1]$ the cytotoxic drug dose (the control). With interpolation $h(-1) = 0$, $h(1) = 1$, double-well potential $\Psi$, proliferation, apoptosis, consumption and supply rates $\mathcal{P}, \mathcal{A}, \mathcal{C}, \mathcal{B} \ge 0$, drug kill rate $\alpha > 0$, vascular nutrient level $\sigma_S$, and positive constants $A, B$ (related to the interfacial thickness and surface tension),

$$\begin{aligned}
\partial_t\varphi &= \Delta\mu + (\mathcal{P}\sigma - \mathcal{A} - \alpha u)h(\varphi), \qquad \mu = A\Psi'(\varphi) - B\Delta\varphi,\\
\partial_t\sigma &= \Delta\sigma - \mathcal{C}\sigma h(\varphi) + \mathcal{B}(\sigma_S - \sigma),
\end{aligned}$$

with homogeneous Neumann conditions for $\varphi, \mu, \sigma$ and initial data $\varphi_0, \sigma_0$.

**Control problem with free treatment time.** For $r > 0$, weights $\beta_u, \beta_T > 0$, $\beta_Q, \beta_\Omega, \beta_S \ge 0$, targets $\varphi_Q, \varphi_\Omega$ and a treatment time $\tau \in [0,T]$, minimize

$$J_r(\varphi, u, \tau) = \frac{\beta_Q}{2}\int_0^\tau\!\!\int_\Omega|\varphi - \varphi_Q|^2 + \frac{\beta_\Omega}{2r}\int_{\tau-r}^\tau\!\!\int_\Omega|\varphi - \varphi_\Omega|^2 + \frac{\beta_S}{2r}\int_{\tau-r}^\tau\!\!\int_\Omega(1+\varphi) + \frac{\beta_u}{2}\int_0^T\!\!\int_\Omega|u|^2 + \beta_T\tau$$

over $u \in \mathcal{U}_{\mathrm{ad}} = \{u \in L^\infty(Q) : 0 \le u \le 1\}$ and $\tau$. The averaged terms over $(\tau - r, \tau)$ relax the end-time terms $\int_\Omega|\varphi(\tau) - \varphi_\Omega|^2$ and $\int_\Omega(1 + \varphi(\tau))$ (tumour size at the end of treatment), and $\beta_T\tau$ penalizes long treatment.

**Theorem (well-posedness).** Assume $\varphi_0 \in H^3$ with $\partial_\nu\varphi_0 = 0$, $\sigma_0 \in H^1$ with $0 \le \sigma_0 \le 1$, $0 \le \sigma_S \le 1$, targets $\varphi_Q, \varphi_\Omega \in L^2(Q)$, $h \in C^2(\mathbb{R};[0,1])$ Lipschitz, and $\Psi \in C^3(\mathbb{R};[0,\infty))$ with, for positive constants $k_0,\dots,k_5$ and all $s,t \in \mathbb{R}$, $|\Psi'(s)| \le k_0\Psi(s) + k_1$, $\Psi(s) \ge k_2|s| - k_3$, $|\Psi''(s)| \le k_4(1 + s^2)$ and $|\Psi'(s) - \Psi'(t)| \le k_5(1 + s^2 + t^2)|s - t|$. Then for each $u \in \mathcal{U}_{\mathrm{ad}}$ there is a unique weak solution with

$$\varphi \in L^\infty(0,T;H^2) \cap L^2(0,T;H^3) \cap H^1(0,T;L^2) \cap C^0(\overline{Q}), \qquad 0 \le \sigma \le 1,$$

depending continuously on $u$.

**Theorem (existence of an optimal treatment).** Under the same assumptions there is at least one minimizer $(\varphi_*, u_*, \tau_*)$ of $J_r$; the trivial cases $\tau_* = 0$ and $\tau_* = T$ cannot be excluded.

## Expansion

The quartic potential and the uniform bounds $0 \le \sigma \le 1$ give energy estimates independent of $u$, higher-order estimates on the Cahn–Hilliard part yield the $H^3$ regularity, and existence follows from a fixed-point argument; the solution map is Lipschitz from $L^2(Q)$ controls to the states. Existence of a minimizer follows from the direct method: a minimizing sequence $(u_n, \tau_n)$ has a weak-star convergent control and a convergent time, the uniform state bounds and compactness pass the nonlinear terms to the limit, and $J_r$ is lower semicontinuous along the sequence. The relaxation is what makes the problem tractable: the unrelaxed functional would need $\partial_{tt}\varphi \in L^2$ and time-differentiable controls to differentiate in $\tau$.

## Sources

- Harald Garcke, Kei Fong Lam, Elisabetta Rocca, "Optimal control of treatment time in a diffuse interface model of tumor growth", arXiv:1608.00488 (2016): Section 1 (model and the objective functionals), Section 2 (Assumption 2.1, Theorem 2.1 well-posedness, Theorem 2.2 existence of a minimizer), Sections 3–4 (proofs). <https://doi.org/10.48550/arXiv.1608.00488>
