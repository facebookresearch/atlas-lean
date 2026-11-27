# Optimal combination therapy via Fokker-Planck control of colon cancer immune dynamics

**Model.** In nondimensional variables, the tumor cell population $T$, natural killer cells $N$, cytotoxic CD8$^+$ T cells $L$ and other lymphocytes $C$ follow the de Pillis colon cancer model with chemotherapy dose $u_1$ (doxorubicin) and immunotherapy dose $u_2$ (IL-2), perturbed by independent Wiener processes:

$$ dT = \bigl( a T (1 - bT) - c N T - D T - \alpha_1 u_1 T \bigr) dt + \sigma_1\, dW_1, \qquad dC = (\alpha - \beta C - \alpha_4 u_1 C)\, dt + \sigma_4\, dW_4, $$

$$ dN = (e C - f N - p N T - \alpha_2 u_1 N + \beta_2 u_2 N)\, dt + \sigma_2\, dW_2, \qquad dL = \Bigl( m L + j \frac{T}{k + T} L - q L T + (r_1 N + r_2 C) T - \alpha_3 u_1 L + \beta_3 u_2 L \Bigr) dt + \sigma_3\, dW_3, $$

where $D = d\, \frac{(L/T)^l}{s' + (L/T)^l}$ is the ratio-dependent CD8$^+$ killing term (normalization constants absorbed into $s'$), written compactly as $dX = F(X, U)\, dt + S\, dW$ with $S = \operatorname{diag}(\sigma_1, \dots, \sigma_4)$. Confining $X$ to a bounded Lipschitz domain $\Omega \subset \mathbb{R}^4_+$ (carrying capacities) by reflection, its density $f(x,t)$ solves the Fokker-Planck equation with no-flux boundary condition

$$ \partial_t f + \nabla \cdot (F(x, U) f) = \tfrac{1}{2} \nabla \cdot (S^2 \nabla f) \ \text{ in } \Omega \times (0, T_f), \qquad \Bigl( \tfrac{\sigma_j^2}{2} \partial_{x_j} f - F_j f \Bigr)_j \cdot \hat n = 0 \ \text{ on } \partial\Omega, \qquad f(\cdot, 0) = f_0. $$

The therapy $U = (u_1, u_2)$ ranges over $U_{ad} = \{ U \in L^2(0,T) : 0 \le u_i \le D_i \}$ and minimizes

$$ J(f, U) = \frac{\alpha}{2} \int_Q (f - f^*)^2 \, dx\, dt + \frac{\nu_1}{2} \int_0^T u_1^2\, dt + \frac{\nu_2}{2} \int_0^T u_2^2\, dt $$

for a target density $f^*$ concentrated on low tumor burden.

**Theorem.**

1. (Proposition 1) For non-negative $f_0 \in H^1(\Omega)$ and $U \in U_{ad}$, the Fokker-Planck system has a unique non-negative solution $f \in L^2(0, T_f; H^1(\Omega)) \cap C([0, T_f]; L^2(\Omega))$.
2. (Proposition 2) The system is conservative: $\int_\Omega f(x,t)\, dx = \int_\Omega f_0\, dx$ for all $t$.
3. (Proposition 3) $\| f(t) \|_{L^2(\Omega)} \le \| f_0 \|_{L^2(\Omega)} \exp\bigl( \| S^{-1} \|_2^2 N^2 t \bigr)$ with $N = \sup_{\Omega \times U_{ad}} |F|$.
4. (Existence of optimal therapies) There is $(f^*_{\mathrm{opt}}, U^*) \in C([0, T_f]; H^1(\Omega)) \times U_{ad}$ with $f^*_{\mathrm{opt}}$ solving the Fokker-Planck system for $U^*$ and $U^*$ minimizing $J$ over $U_{ad}$.

## Expansion

Well-posedness is a Galerkin argument for a linear parabolic equation with bounded drift: testing with $f$ and using Young's inequality, $\frac{1}{2} \frac{d}{dt} \|f\|^2 + \frac{1}{2} \| S \nabla f \|^2 \le \|F f\| \|\nabla f\|$, which absorbs into the diffusion and yields the $L^2$ growth bound of Proposition 3 by Gronwall. The no-flux condition makes the divergence form integrate to zero, giving mass conservation, and a maximum principle keeps $f$ non-negative, so $f(\cdot, t)$ stays a probability density. For existence of an optimum, a minimizing sequence of controls is weakly compact in $L^2$, the corresponding densities are bounded in $L^2(H^1)$ with bounded time derivatives, so they converge strongly in $L^2(Q)$ by Aubin-Lions; the control enters the drift linearly, so the limit solves the state equation, and $J$ is weakly lower semicontinuous. Working with the density rather than single trajectories lets the optimized therapy account for the whole distribution of patient-level stochastic tumor-immune outcomes.

## Sources

- Souvik Roy, Suvra Pal, "Optimal Personalized Therapies in Colon Cancer Induced Immune Response using a Fokker‐Planck Framework", Mathematics and Computer Science Volume 2 (2023), 33–47, <https://doi.org/10.1002/9781119896715.ch3>. Published version of arXiv:2209.03812, cited next; locators there refer to the arXiv version.
- Souvik Roy, Suvra Pal, "Optimal personalized therapies in colon-cancer induced immune response using a Fokker-Planck framework", arXiv (2022). Control framework section, Propositions 1-3 and the existence theorem of the theoretical results section. <https://doi.org/10.48550/arXiv.2209.03812>
