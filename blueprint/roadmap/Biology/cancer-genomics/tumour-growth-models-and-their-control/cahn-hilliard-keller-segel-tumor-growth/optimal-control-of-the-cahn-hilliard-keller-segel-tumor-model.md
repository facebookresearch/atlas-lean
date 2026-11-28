# Optimal control of vasculature in the Cahn–Hilliard–Keller–Segel tumor model

**Problem.** For the multi-species Cahn–Hilliard–Keller–Segel tumor model on a bounded smooth domain $\Omega \subset \mathbb{R}^2$, with the control $u$ entering as a source term in the vasculature equation $\partial_t a - \Delta a + \chi_a\nabla\cdot(a\nabla\sigma) = a - a^2 + u$, minimize the tracking cost

$$
\mathcal{J}(\phi,u) = \frac{b_1}{2}\int_Q |\phi - \phi_Q|^2 + \frac{b_2}{2}\int_\Omega |\phi(T) - \phi_\Omega|^2 + \frac{b_3}{2}\int_Q |u|^2
$$

over the admissible set

$$
\mathcal{U}_{ad} = \{ u \in L^\infty(Q) : 0 \le u \le u_{\max} \ \text{a.e. in } Q \},
$$

where $b_1, b_2 \ge 0$, $b_3 > 0$, $u_{\max} \in L^\infty(Q)$ is nonnegative, $\phi_Q$ and $\phi_\Omega$ are target tumor distributions (clinical targets), and $\phi$ is the tumor component of the unique solution of the state system for the control $u$. The structural and initial-data hypotheses are those of the well-posedness theorem.

**Theorem (existence of an optimal control).** The problem has at least one solution: there is $u^* \in \mathcal{U}_{ad}$ with $\mathcal{J}(\phi^*,u^*) \le \mathcal{J}(\phi,u)$ for every $u \in \mathcal{U}_{ad}$.

**Theorem (first-order necessary condition).** Let $u^* \in \mathcal{U}_{ad}$ be optimal and let $(p_1,\dots,p_5)$ be the unique solution of the associated linear adjoint problem (backward in time, with $(p_3,p_4,p_5)(T) = 0$). Then

$$
\int_Q (p_3 + b_3 u^*)(u - u^*) \ge 0 \quad \text{for every } u \in \mathcal{U}_{ad},
$$

so $u^*$ is the $L^2(Q)$-orthogonal projection of $-p_3/b_3$ onto $\mathcal{U}_{ad}$, i.e. $u^* = \max\{0, \min\{u_{\max}, -p_3/b_3\}\}$ pointwise. Here $p_3$ is the adjoint variable paired with the vasculature equation.

## Expansion

Existence follows by the direct method: a minimizing sequence is bounded in $L^\infty(Q)$, hence weakly-star compact; the uniform stability estimate (independent of $u$) and compact embeddings let one pass to the limit in the state system, and the cost is weakly lower semicontinuous. For the optimality condition, the control-to-state map is not Fréchet differentiable on an open set in $L^\infty$, but the solution of the linearized system for a direction $h$ with $u^* + h \in \mathcal{U}_{ad}$ satisfies $\|\mathcal{S}(u^* + h) - \mathcal{S}(u^*) - \text{(linearized solution)}\| = o(\|h\|_{L^2(Q)})$, which is enough to differentiate the reduced cost along admissible directions. Introducing the adjoint system removes the linearized state from the derivative and gives the variational inequality. The separation property of $\phi$ keeps $F''(\phi^*)$ bounded, which the linearized and adjoint problems require.

## Depends on

- [Well-posedness of the multi-species Cahn–Hilliard–Keller–Segel tumor model](well-posedness-of-the-multi-species-cahn-hilliard-keller-segel-tumor-model.md)

## Sources

- Pierluigi Colli, Gianni Gilardi, Andrea Signori, Jürgen Sprekels, "Solvability and optimal control of a multi-species Cahn–Hilliard–Keller–Segel tumor growth model", ESAIM: Control, Optimisation and Calculus of Variations 31 (2025), 85, <https://doi.org/10.1051/cocv/2025070>. Published version of arXiv:2407.18162, cited next; locators there refer to the arXiv version.
- Pierluigi Colli, Gianni Gilardi, Andrea Signori, Jürgen Sprekels, "Solvability and optimal control of a multi-species Cahn-Hilliard-Keller-Segel tumor growth model," arXiv 2024. Section 6, Theorem 6.1 (existence of an optimal control); Section 7, Theorems 7.1–7.3 (linearized problem, differentiability of the control-to-state map, adjoint problem) and Theorem 7.4 (necessary optimality condition). <https://doi.org/10.48550/arXiv.2407.18162>
