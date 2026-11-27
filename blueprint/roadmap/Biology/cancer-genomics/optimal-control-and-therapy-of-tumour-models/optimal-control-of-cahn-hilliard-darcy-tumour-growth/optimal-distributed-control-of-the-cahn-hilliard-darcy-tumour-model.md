# Optimal distributed control of the Cahn–Hilliard–Darcy tumour model with mass sources

**Setting.** In a bounded smooth domain $\Omega \subset \mathbb{R}^2$ over $(0,T)$, let $\varphi \in [-1,1]$ be the difference of volume fractions ($\varphi = 1$ tumour, $\varphi = -1$ healthy tissue), $\mu$ the chemical potential, $u$ the volume-averaged velocity and $P$ the pressure, solving the Cahn–Hilliard–Darcy system with mass sources

$$\nu(\varphi)u = -\nabla P + \mu\nabla\varphi, \qquad \operatorname{div}u = S, \qquad \varphi_t + \operatorname{div}(\varphi u) = \Delta\mu + S + R, \qquad \mu = -\Delta\varphi + \Psi'(\varphi),$$

with $u\cdot n = \partial_n\mu = \partial_n\varphi = 0$ on $\partial\Omega$ and $\varphi(0) = \varphi_0$. Here $S$ is a given mass exchange (proliferation and death) and $R$ is a control, e.g. a drug or nutrient supply. Assumptions: the potential is singular, $\Psi(s) = F(s) - \frac{\Theta_0}{2}s^2$ with $F \in C([-1,1]) \cap C^2(-1,1)$, $F'(\pm 1^\mp) = \pm\infty$, $F'' \ge \Theta > 0$, $\Theta_0 > \Theta$, and, for some $\kappa\in(0,1)$, $F''$ non-decreasing on $[1-\kappa,1)$ and non-increasing on $(-1,-1+\kappa]$ (the source's (A1)); moreover $F \in C^5(-1,1)$, $F'''(s)\,s \ge 0$ and $F^{(4)}(s) > 0$ for $s \in (-1,-1+\kappa] \cup [1-\kappa,1)$, and $|F''(s)| \le C e^{C|F'(s)|}$ for all $s \in (-1,1)$ with a constant $C>0$ (the source's (A1)′, used by the strong well-posedness Theorem 3.1 and through it by Theorems 4.1, 5.2 and 6.1) (the Flory–Huggins potential $\frac{\Theta}{2}[(1+s)\ln(1+s) + (1-s)\ln(1-s)] - \frac{\Theta_0}{2}s^2$ satisfies all of these and is the model case); the viscosity is unmatched, $\nu \in C^3(\mathbb{R})$ with $0 < \nu_* \le \nu, \nu', \nu'', \nu''' \le \nu^*$.

Given targets $\varphi_\Omega \in H^1(\Omega)$, $\varphi_Q \in L^2(Q)$ and weights $\alpha_1, \alpha_2, \beta \ge 0$ (not all zero), consider

$$\min\ \mathcal{J}(\varphi,R) = \frac{\alpha_1}{2}\|\varphi(T) - \varphi_\Omega\|_{L^2(\Omega)}^2 + \frac{\alpha_2}{2}\|\varphi - \varphi_Q\|_{L^2(Q)}^2 + \frac{\beta}{2}\|R\|_{L^2(Q)}^2$$

over admissible controls $\mathcal{U}_{\mathrm{ad}} = \{R \in \mathcal{U} \cap L^\infty(Q) : \|R\|_{\mathcal{U}} \le r_1,\ \|R\|_{L^1(Q)} \le r_0,\ R_{\min} \le R \le R_{\max}\}$, where $\mathcal{U} = L^2(0,T;H^1(\Omega)) \cap H^1(0,T;(H^1(\Omega))')$ and $r_0 > 0$ is chosen from $\varphi_0$ so that the mean of $\varphi$ stays in $(-1,1)$.

**Theorem.**

1. *(State system.)* For $\varphi_0 \in H^2(\Omega)$ with $\overline{\varphi_0} \in (-1,1)$, $-\Delta\varphi_0 + F'(\varphi_0) \in H^1(\Omega)$ and sources satisfying the mean constraint, there is a unique global strong solution, with $\varphi \in C([0,T];H^3) \cap L^2(0,T;H^5) \cap H^1(0,T;H^1)$, which is strictly separated from the pure phases: $\|\varphi(t)\|_{C(\overline{\Omega})} \le 1 - \delta_1$ for all $t$, for some $\delta_1 \in (0,1)$. The control-to-state map $R \mapsto \varphi$ is Lipschitz from $L^2(Q)$.
2. *(Existence.)* The control problem has at least one globally optimal control $R^*$.
3. *(First-order conditions.)* Every locally optimal control $R^*$ with adjoint state $(w^*,\pi^*,\rho^*,\zeta^*)$ satisfies

$$\int_Q(\rho^* + \beta R^*)(R - R^*)\,dx\,dt \ge 0 \quad \text{for all } R \in \mathcal{U}_{\mathrm{ad}}.$$

4. *(Second-order sufficiency.)* If $\beta > 0$, $R^*$ satisfies the variational inequality, and $\widehat{\mathcal{J}}''(R^*)[h,h] > 0$ on the critical cone, then there are $\lambda, \theta > 0$ with $\widehat{\mathcal{J}}(R) \ge \widehat{\mathcal{J}}(R^*) + \theta\|R - R^*\|_{L^2(Q)}^2$ whenever $\|R - R^*\|_{L^2(Q)} < \lambda$; thus $R^*$ is a strict local minimizer.

## Expansion

The singular potential keeps $\varphi$ in $[-1,1]$, but its derivative blows up at $\pm1$; the key a priori estimate is the uniform separation property, which in two dimensions follows from higher-order energy estimates and makes $\Psi$ effectively smooth along the solution. The mass constraint on $R$ ensures that the spatial mean of $\varphi$, which evolves by $\frac{d}{dt}\overline{\varphi} = \overline{R}$ (since $S$ has zero mean), stays away from $\pm 1$. With strong solutions and Lipschitz dependence, the control-to-state map is Fréchet (and twice) differentiable; existence follows from weak compactness of $\mathcal{U}_{\mathrm{ad}}$ and weak lower semicontinuity of $\mathcal{J}$, the first-order condition from the linearized system and its adjoint, and the quadratic growth from a standard second-order argument on the reduced cost.

## Sources

- Marco Abatangelo, Cecilia Cavaterra, Maurizio Grasselli and Hao Wu, "Optimal Distributed Control for a Cahn-Hilliard-Darcy System with Mass Sources, Unmatched Viscosities and Singular Potential", arXiv:2308.01569 (2023), Section 3 assumptions (A1), (A1)′, (A2) and (A3), Theorem 3.1, Theorem 4.1, Theorems 5.1–5.2 and Theorem 6.1, <https://doi.org/10.48550/arXiv.2308.01569>. Published version: ESAIM Control Optim. Calc. Var., 30 (2024), Article number: 52, 49 pages, <https://doi.org/10.1051/cocv/2024041>.
