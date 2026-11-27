# Stationary multiphase model of tumor cord growth

**Model.** A tumor cord is a cylinder of tumor cells growing around a blood vessel, which supplies a nutrient. It is modeled as a saturated mixture of proliferating cells, extracellular fluid and a rigid extracellular matrix, embedded in a host tissue. Neglecting matrix remodeling and nondimensionalizing reduces the model to equations for the cell volume ratio $\phi$ and the nutrient concentration $c$. In the stationary one-dimensional problem across the cord, with the vessel wall at $x = 0$ and the tumor–host interface (cord width $w$) rescaled to $x = 1$:

$$
\begin{cases}
-\partial_x^2F(\phi) = w^2\,g(\phi)\,\Gamma(c) & \text{in } (0,1),\\
-\partial_x^2c + \alpha w^2\phi\,c = 0 & \text{in } (0,1),\\
\partial_x\phi = 0,\quad c = 1 & x = 0,\\
\phi = \phi_0,\quad \partial_xc = 0 & x = 1 .
\end{cases}
$$

Here $F$, with $F'(\phi) = \phi\,(\phi\Sigma(\phi))'$, is a generalized stress function built from the cell stress $\Sigma$. $g$ is the specific growth function, $\Gamma(c)$ regulates proliferation (above a critical nutrient level) or death (below it), $\alpha > 0$ is the consumption rate, and $\phi_0 \in (0,1)$ is the stress-free cell density.

**Assumptions.** $F \in C^1([0,1])$ with $F' \ge 0$, $F' > 0$ on $(0,1]$, $F(0) = 0$, $F(1) = 1$; $g$ is Lipschitz on $[0,1]$ with constant $L_g$ and $g \ge 0$ there; $\Gamma$ is Lipschitz on $[0,1]$.

**Theorem.**
1. (Nutrient) For each admissible $\phi$ the nutrient problem has a unique $C^2$ solution $c$. It is monotonically decreasing in $x$, with maximum $1$ at the vessel wall.
2. (Existence) Let $\beta = \max(\beta_1,\beta_2)$ with $\beta_1 = \sqrt{C_Pg_{\max}\Gamma_{\max}/(F(\phi_0) - F(\epsilon))}$ and $\beta_2 = C_P\sqrt{L_g\Gamma_{\max}L_f}$, where $C_P$ is a Poincaré constant, $g_{\max}$ and $\Gamma_{\max}$ bound $g$ and $\Gamma$, $L_f$ is the Lipschitz constant of $f = F^{-1}$ on $[F(\epsilon),1]$, and $\epsilon \in (0,\phi_0)$ is a positivity threshold. If $\beta w < 1$, the stationary problem has a solution $(\phi,c)$ with $\|1 - c\|_\infty \le \alpha w^2\|\phi\|_{L^2}$.
3. (Closeness to the stress-free state) Every solution satisfies $\|\phi - \phi_0\|_\infty \le \dfrac{g_{\max}}{L_gC_P}(\beta_2w)^2$.
4. (Free boundary) If $\phi$ also satisfies the free-boundary condition that fixes the stationary cord width, then, if $\Gamma$ is nondecreasing on $[0,1]$ with $\Gamma(0) < 0 < \Gamma(1)$, $\phi \ge \phi_0$ throughout the cord.

Thin enough cords (small $w$) therefore have a steady state close to the stress-free density, with nutrient depleted by at most $O(w^2)$ from the vessel to the interface. A perturbative argument then identifies the steady cord width.

## Expansion

Rescaling $x \to wx$ turns the free-boundary problem into a fixed-domain problem with $w$ in the coefficients. One defines solution operators: $A_1$ maps $\phi$ to the nutrient solution $c$, and $A_2$ maps $c$ to the solution $\phi$ of the stress equation. Both are Lipschitz, and $A_1$ is compact, so a fixed point of $A = A_2\circ A_1$ follows from Schauder's theorem. The smallness condition $\beta w < 1$ keeps $\phi$ in the admissible set where $F$ is invertible, and the maximum principle gives monotonicity of $c$. The a priori bounds follow from integrating the equations twice with the Poincaré inequality, each integration producing a factor $w^2$.

## Sources

- Andrea Tosin, "Multiphase modeling and qualitative analysis of the growth of tumor cords", arXiv:0906.5077 (2009), Section 2 (model), Section 5 (Assumptions 1–4, Propositions 1–4, Theorems 5, 6 and 7), <https://doi.org/10.48550/arXiv.0906.5077>.
