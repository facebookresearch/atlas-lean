# Optimality conditions for the treatment time and dose in a Cahn–Hilliard tumour model

**Setting.** Consider the [free-treatment-time control problem](optimal-treatment-time-in-a-cahn-hilliard-tumour-model.md) for the Cahn–Hilliard–nutrient tumour model, with relaxed objective $J_r(\varphi, u, \tau)$, admissible doses $\mathcal{U}_{\mathrm{ad}} = \{0 \le u \le 1\}$ and treatment time $\tau \in [0,T]$. Assume in addition $\varphi_Q \in H^1(0,T;L^2)$ and $\varphi_\Omega \in H^1(-r,T;L^2)$, and extend $\varphi(t) = \varphi_0$ for $t < 0$.

**Adjoint system.** For a control $u$ with state $(\varphi, \mu, \sigma)$ and time $\tau_*$, there is a unique triplet $(p, q, r)$ with $p \in L^2(0,\tau_*;H^2) \cap C^0([0,\tau_*];L^2)$, $q \in L^2(0,\tau_*;L^2)$ and $r \in L^2(0,\tau_*;H^2) \cap H^1(0,\tau_*;L^2)$ solving, backward in time and weakly,

$$\begin{aligned}
-\partial_tp &= -B\Delta q + A\Psi''(\varphi)q - h'(\varphi)\big(\mathcal{C}\sigma r - (\mathcal{P}\sigma - \mathcal{A} - \alpha u)p\big) + \beta_Q(\varphi - \varphi_Q) + \tfrac{1}{2r}\chi_{(\tau_*-r,\tau_*)}\big(2\beta_\Omega(\varphi - \varphi_\Omega) + \beta_S\big),\\
q &= \Delta p, \qquad -\partial_tr = \Delta r - \mathcal{B}r - \mathcal{C}h(\varphi)r + \mathcal{P}h(\varphi)p,
\end{aligned}$$

with homogeneous Neumann conditions and zero terminal data at $\tau_*$ (the signs follow from the weak form in the source).

**Theorem (first-order necessary conditions).** Let $(u_*, \tau_*)$ be a minimizer with state $(\varphi_*, \mu_*, \sigma_*)$ and adjoint $(p, q, r)$. Then

$$\int_0^T\!\!\int_\Omega\beta_uu_*(u - u_*) - \int_0^{\tau_*}\!\!\int_\Omega\alpha h(\varphi_*)p\,(u - u_*) \ge 0 \qquad \text{for all } u \in \mathcal{U}_{\mathrm{ad}},$$

so, extending $p$ by zero after $\tau_*$, $u_*$ is the $L^2(Q)$-projection of $\beta_u^{-1}\alpha h(\varphi_*)p$ onto $[0,1]$. Moreover, with

$$G(\tau) = \beta_T + \frac{\beta_Q}{2}\|(\varphi_* - \varphi_Q)(\tau)\|^2_{L^2} + \frac{\beta_S}{2r}\int_\Omega\big(\varphi_*(\tau) - \varphi_*(\tau - r)\big) + \frac{\beta_\Omega}{2r}\Big(\|(\varphi_* - \varphi_\Omega)(\tau)\|^2_{L^2} - \|(\varphi_* - \varphi_\Omega)(\tau - r)\|^2_{L^2}\Big),$$

the optimal time satisfies $G(\tau_*) \ge 0$ if $\tau_* = 0$, $G(\tau_*) = 0$ if $\tau_* \in (0,T)$, and $G(\tau_*) \le 0$ if $\tau_* = T$.

## Depends on

- [Optimal treatment time in a Cahn–Hilliard tumour model](optimal-treatment-time-in-a-cahn-hilliard-tumour-model.md)

## Expansion

The control-to-state map is Fréchet differentiable, its derivative solving the linearized state equations, so the reduced functional $\mathcal{J}(u,\tau)$ is differentiable in $u$ and the variational inequality follows from convexity of $\mathcal{U}_{\mathrm{ad}}$ after eliminating the linearized state with the adjoint. Differentiability in $\tau$ uses only $\varphi \in C^0([0,T];L^2)$ and the regularity of the targets, because the relaxed terms are averages over $(\tau - r, \tau)$: $G(\tau)$ is exactly $\partial_\tau\mathcal{J}$, and the three-case condition is the Karush–Kuhn–Tucker condition for minimizing over $[0,T]$. Interior optimality balances the marginal cost $\beta_T$ of treating longer against the marginal change in tumour size and tracking error over the last window, which is the PDE analogue of the transversality condition for free-terminal-time ODE control.

## Sources

- Harald Garcke, Kei Fong Lam, Elisabetta Rocca, "Optimal control of treatment time in a diffuse interface model of tumor growth", arXiv:1608.00488 (2016): Section 2 (Theorems 2.3–2.4 linearized state equations and Fréchet differentiability, Theorem 2.5 adjoint equations, Assumption 2.2, Theorem 2.6 derivative in $\tau$, Theorem 2.7 first-order necessary optimality conditions), Sections 5–6 (proofs). <https://doi.org/10.48550/arXiv.1608.00488>
