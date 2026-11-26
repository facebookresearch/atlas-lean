# Martingale solutions of stochastic Keller–Segel with nonlocal Fisher–KPP source

**Model.** In a smooth bounded domain $\mathcal O \subset \mathbb R^d$, $d \ge 3$, with Neumann boundary conditions, a cell density $u \ge 0$ obeys the stochastic parabolic–elliptic Keller–Segel system
$$du = \Big[\Delta u - \nabla\cdot(u\nabla c) + u^{\alpha}\Big(1 - \int_{\mathcal O}u^{\beta}\,dx\Big)\Big]dt + \sigma(u)\,dW(t), \qquad -\Delta c + c = u,$$
driven by a cylindrical Wiener process $W$, with a nonlocal Fisher–KPP source (growth $u^\alpha$ regulated by the total $\int u^\beta$) and super-linear multiplicative noise: $\sigma : L^\gamma(\mathcal O) \to L_2(U_0,L^2(\mathcal O))$ satisfies
$$\|\sigma(u)\|_{L_2}^2 \le C\|u\|_{L^\gamma}^{\gamma}, \qquad \|\sigma(u)-\sigma(v)\|_{L_2}^2 \le C\big(\|u\|_{L^\gamma}^{\gamma-2} + \|v\|_{L^\gamma}^{\gamma-2}\big)\|u - v\|_{L^\gamma}^2,$$
for some $\gamma \ge 2$, and acts locally ($\sigma(u)$ and $\sigma(v)$ agree on sets where $u = v$).

**Theorem.** Let $\alpha > 1$, $\beta > 1$, $\gamma \ge 2$ with $\alpha + 1 > \beta$ and
$$\max\{3,\ \gamma,\ \alpha + 1\} < \frac{2}{d+2}\,(\alpha - 1 + \beta).$$
Then for every non-negative initial datum $u_0 \in L^2(\Omega;L^2(\mathcal O))$ (approximated by Galerkin data with bounded second moments) and every $T>0$ there is a global non-negative martingale solution on $[0,T]$. No smallness of the data is required: the condition says that the nonlocal source dominates both the chemotactic aggregation and the noise.

## Expansion

The Galerkin system is truncated by a cut-off of the $L^2$ norm, which gives pathwise unique local strong solutions; positivity of the approximations is proved because the nonlocal source does not preserve sign by comparison alone. The nonlocal term $-u^\alpha\int u^\beta$ supplies dissipation of order $\|u\|_{L^{\alpha-1+\beta}}$-type that, by the exponent condition and Gagliardo–Nirenberg interpolation, absorbs the aggregation term and the Itô correction from $\sigma$, giving uniform moment bounds and removal of the cut-off. Since these bounds are not in a Hilbert-space setting, the authors prove a generalized compactness and tightness criterion and conclude with Skorokhod–Jakubowski representation.

## Sources

- Qian Li, Li Chen and Jinhuan Wang, "Martingale Solutions to a Stochastic Keller-Segel System with nonlocal Source and Super-linear Noise", arXiv:2606.11774 (2026), Theorem 1 (global existence), Theorems 2–4 (Galerkin well-posedness) and Theorems 5–6 (compactness and tightness criteria), <https://doi.org/10.48550/arXiv.2606.11774>.
