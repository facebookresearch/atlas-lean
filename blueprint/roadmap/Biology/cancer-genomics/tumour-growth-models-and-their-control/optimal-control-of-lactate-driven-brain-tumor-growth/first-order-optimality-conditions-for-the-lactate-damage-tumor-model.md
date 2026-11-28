# First-order optimality conditions for the lactate-damage tumor model

Consider the brain tumor control problem with cytotoxic control $\chi_1$, lactate-targeting control $\chi_2$, state $(\varphi,\sigma,\mathbf{u},z)$ (tumor density, lactate, displacement, damage), admissible set $\mathcal{U}_{ad}$ and tracking cost $\mathcal{J}$ with weights $\alpha_1,\dots,\alpha_9 \ge 0$, as in the existence result, under the hypotheses (H1)–(H12) stated there. Let $\mathcal{S} : \boldsymbol{\chi} \mapsto (\varphi,\sigma,\mathbf{u},z)$ be the control-to-state operator.

**Theorem.**

1. (Differentiability) $\mathcal{S}$ is Fréchet differentiable on an open neighbourhood $\mathcal{U}_R$ of $\mathcal{U}_{ad}$, and $D\mathcal{S}(\boldsymbol{\chi})\mathbf{h} = (\xi,\rho,\boldsymbol{\omega},\zeta)$ is the unique solution of the state system linearized at $\mathcal{S}(\boldsymbol{\chi})$ with direction $\mathbf{h}$ and zero initial data.
2. (Adjoint system) For an optimal control $\boldsymbol{\chi}^*$ with state $(\varphi^*,\sigma^*,\mathbf{u}^*,z^*)$ the backward adjoint system has a unique weak solution $(q, r, \mathbf{v}, s)$ with terminal data

$$q(T) = \alpha_2(\varphi^*(T) - \varphi_\Omega) + \alpha_3, \qquad r(T) = \alpha_5(\sigma^*(T) - \sigma_\Omega), \qquad \mathbf{v}(T) = 0, \qquad s(T) = \alpha_8.$$

3. (Variational inequality) Every optimal control satisfies, for all $\boldsymbol{\chi} = (\chi_1,\chi_2) \in \mathcal{U}_{ad}$,

$$-\int_Q \varphi^*\Big(1 - \frac{\varphi^*}{N}\Big)(\chi_1 - \chi_1^*)\, q + \int_Q S(\varphi^*, z^*)(\chi_2 - \chi_2^*)\, r + \alpha_9 \int_Q \boldsymbol{\chi}^* \cdot (\boldsymbol{\chi} - \boldsymbol{\chi}^*) \ge 0.$$

In particular, when $\alpha_9 > 0$ each optimal control is the pointwise projection of the corresponding adjoint-weighted sensitivity onto the box constraints (for $\chi_2$; for $\chi_1$ up to the additional $L^2(H^1)$-ball constraint).

## Depends on

- [Existence of optimal chemotherapy and lactate-targeting controls](existence-of-optimal-controls-for-the-lactate-damage-tumor-model.md)

## Expansion

Since $\mathcal{U}_{ad}$ is convex, optimality gives $D(\mathcal{J}\circ\mathcal{S})(\boldsymbol{\chi}^*)(\boldsymbol{\chi} - \boldsymbol{\chi}^*) \ge 0$. Fréchet differentiability of $\mathcal{S}$ is proved by showing the remainder $\mathcal{S}(\boldsymbol{\chi}+\mathbf{h}) - \mathcal{S}(\boldsymbol{\chi}) - (\xi,\rho,\boldsymbol{\omega},\zeta)$ is $o(\|\mathbf{h}\|)$, using the uniform bounds and the separation of $z$ from $0$ and $1$ (so the damage nonlinearity is smooth along the trajectory). The adjoint system is chosen so that integrating its pairing with the linearized system eliminates the linearized states, leaving only the terms where the controls enter: the cytotoxic control through $-\chi_1\varphi(1 - \varphi/N)$ and the lactate drug through $\chi_2 S(\varphi,z)$.

## Sources

- Giulia Cavalleri, Alain Miranville, "Optimal control on a brain tumor growth model with lactate metabolism, viscoelastic effects, and tissue damage", Discrete and Continuous Dynamical Systems - B 32 (2026), 219–245, <https://doi.org/10.3934/dcdsb.2025129>. Published version of arXiv:2503.17049, cited next; locators there refer to the arXiv version.
- Giulia Cavalleri, Alain Miranville, "Optimal control on a brain tumor growth model with lactate metabolism, viscoelastic effects, and tissue damage", arXiv (2025). Proposition 4.2, Theorem 5.1, Corollary 5.2, Proposition 6.1, Theorem 6.2. <https://doi.org/10.48550/arXiv.2503.17049>
