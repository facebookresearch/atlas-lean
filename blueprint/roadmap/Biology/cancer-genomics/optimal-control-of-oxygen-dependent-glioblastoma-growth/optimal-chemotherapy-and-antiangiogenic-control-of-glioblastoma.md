# Optimal chemotherapy and antiangiogenic control of oxygen-dependent glioblastoma growth

**State system.** Let $u(t)$ be the glioblastoma cell density and $\sigma(t)$ the oxygen concentration on $[0,T]$. With a chemotherapy control $\mathsf{c}(t)$ and an antiangiogenic control $\mathsf{s}(t)$, both in $[0,1]$,

$$

\begin{cases}
u' = \rho(\sigma)\, u(\alpha - u) - \kappa\, \mathsf{c}\, u\, \sigma, \\[2pt]
\sigma' = P_{er} S_v (\beta - \sigma) - \dfrac{A_{ox}\, u\, \sigma}{k_{ox} + \sigma} + (1 - \mathsf{s})\, S_c\, u, \\[2pt]
u(0) = u_0, \quad \sigma(0) = \sigma_0 .
\end{cases}

$$

Here $\alpha > 0$ is the carrying capacity, $\rho \in C^1([0,\infty))$ is an oxygen-dependent proliferation rate with bounded derivative and $\rho \ge \rho_{\min} > 0$ (e.g. $\rho(\sigma) = \frac{\hat\rho}{\alpha}\left(\frac{\sigma}{\beta} + b\left(1 - \frac{\sigma}{\beta}\right)\right)$, $b \in (0,1]$), $\kappa > 0$ the chemotherapy efficacy, $P_{er}, S_v > 0$ the vascular permeability and density, $\beta > 0$ the reference oxygen level, $A_{ox}, k_{ox} > 0$ Michaelis–Menten consumption constants, and $S_c > 0$ the strength of tumor-induced angiogenesis, which the antiangiogenic therapy suppresses.

**Theorem (existence, uniqueness and invariant bounds).** Let $\mathsf{c}, \mathsf{s} \in L^\infty(0,T)$ with $0 \le \mathsf{c}, \mathsf{s} \le 1$ a.e., and suppose $0 \le u_0 \le \alpha$ and $0 \le \sigma_0 \le C_\sigma$, where

$$

C_\sigma = \beta + \frac{S_c\, \alpha}{P_{er} S_v} .

$$

Then the state system has a unique absolutely continuous solution on $[0,T]$, and $0 \le u(t) \le \alpha$ and $0 \le \sigma(t) \le C_\sigma$ for a.e. $t \in [0,T]$.

**Control problem.** Minimize

$$

J = \int_0^T \left[ \frac{k_1}{2} u^2 + \frac{k_2}{2}(\sigma - \sigma_d)^2 + k_3\, \mathsf{c} + k_4\, \mathsf{s} \right] dt + \frac{l_1}{2} u(T)^2 + \frac{l_2}{2}\big(\sigma(T) - \sigma_{dT}\big)^2

$$

over the admissible set

$$

\mathcal{U}_{ad} = \left\{ [\mathsf{c}, \mathsf{s}] \in L^\infty(0,T)^2 : 0 \le \mathsf{c}, \mathsf{s} \le 1,\ \int_0^T \mathsf{c}(t)\, dt \le c_{\max} \right\},

$$

with positive bounded weights $k_i$, $l_1, l_2 > 0$, a target oxygen profile $\sigma_d \in L^\infty(0,T)$, a terminal target $\sigma_{dT}$, and a total chemotherapy budget $c_{\max} > 0$.

**Theorem (existence of an optimal control).** Under the hypotheses above there is at least one global optimal control $[\mathsf{c}^*, \mathsf{s}^*] \in \mathcal{U}_{ad}$ for the reduced cost $\hat J([\mathsf{c},\mathsf{s}]) = J(u(\mathsf{c},\mathsf{s}), \sigma(\mathsf{c},\mathsf{s}), \mathsf{c}, \mathsf{s})$. First-order necessary conditions are derived from the Pontryagin minimum principle with an adjoint system, using a characterization of the projection onto box constraints with an integral budget.

## Expansion

The right-hand side is measurable in $t$ and locally Lipschitz in $(u,\sigma)$, so Carathéodory theory gives a unique maximal solution. Comparison arguments then trap it: $0$ is a subsolution for both equations, the constant $\alpha$ is a supersolution for $u$ because the chemotherapy term is nonpositive, and since $u \le \alpha$ and $\mathsf{s} \ge 0$, $\sigma' \le P_{er}S_v(\beta - \sigma) + S_c\alpha$, whose equilibrium is $C_\sigma$. Boundedness extends the solution to $[0,T]$. Existence of an optimal control follows from a general existence theorem for optimal control problems (Clarke, Theorem 23.11): the admissible set is convex and closed, the dynamics are affine in the controls and the running cost is convex in them, and the states are uniformly bounded. The paper then approximates the state and adjoint systems with sequential physics-informed neural networks and updates the controls by gradient descent with Armijo line search.

## Sources

- Juan J. Forero-Hernández, Élder J. Villamizar-Roa, "Modeling of an ODE-constrained optimization problem describing tumor dynamics, and numerical approximation via sequential physics-informed neural networks," arXiv 2026. Section 2, Theorem 2.1 (existence, uniqueness and bounds), Theorem 2.2 (existence of a global optimal control), Proposition 2.3 (projection onto a set with an integral constraint). <https://doi.org/10.48550/arXiv.2608.18974>
