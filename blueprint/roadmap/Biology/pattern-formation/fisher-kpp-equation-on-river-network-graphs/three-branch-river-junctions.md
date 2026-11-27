# Fisher–KPP advection–diffusion at a three-branch river junction

Consider three half-lines meeting at a vertex $0$, each carrying $\partial_tw_i - \partial_{xx}w_i + \beta_i\partial_xw_i = w_i - w_i^2$ with flow speed $\beta_i > 0$ and cross-section $a_i > 0$, continuity of $w_i(t,0)$ across branches, and the Kirchhoff condition at the vertex. The initial data $w_{i,0}$ are nonnegative and continuous on the closed branches, have a common value $w_{i,0}(0)$ at the vertex, vanish far from the junction (for large $|x|$ on every branch), and are not all identically $0$. For these data the problem has a unique nonnegative classical solution.

For a junction value $\alpha \in (0,1)$, the **steady-state problem** asks for a solution $(\varphi_i)$ of $-\varphi_i'' + \beta_i\varphi_i' = \varphi_i - \varphi_i^2$ with $0 < \varphi_i < 1$ on every branch, $\varphi_i(0) = \alpha$ for every $i$, and the same Kirchhoff condition as the evolution problem.

**Two upper branches, one lower branch.** Upper branches $U_1, U_2 = (-\infty,0)$ flow into $L = (0,\infty)$, with conservation of flow $a_L\beta_L = a_{U_1}\beta_{U_1} + a_{U_2}\beta_{U_2}$ and Kirchhoff condition $a_L\partial_xw_L(t,0) = a_{U_1}\partial_xw_{U_1}(t,0) + a_{U_2}\partial_xw_{U_2}(t,0)$. Locally uniformly as $t\to\infty$:

1. if $\beta_{U_1}, \beta_{U_2} < 2$: $w \to (1,1,1)$;
2. if $\beta_L, \beta_{U_1}, \beta_{U_2} \ge 2$: $w \to (0,0,0)$, with $\|w_{U_i}\|_\infty \to 0$ and $\|w_L\|_\infty \to 1$;
3. if $\beta_{U_1}, \beta_{U_2} \ge 2 > \beta_L$: there is $\alpha_* \in (0,1)$ such that the steady-state problem has no solution for $\alpha < \alpha_*$ and exactly one for $\alpha = \alpha_*$; this solution is increasing in the flow direction on every branch, and $w$ converges to it;
4. if $\beta_{U_1} \ge 2 > \beta_{U_2}$: there is $\alpha_{**} \in (0,1)$ such that the steady-state problem has exactly one solution for each $\alpha \in [\alpha_{**},1)$ and none for $\alpha < \alpha_{**}$; $w$ converges to the solution with $\alpha = \alpha_{**}$, which tends to $1$ up the slow branch $U_2$ and to $0$ up the fast branch $U_1$ (decreasing in the flow direction on $U_2$, increasing on $U_1$ and $L$). Symmetrically with $U_1, U_2$ exchanged.

**One upper branch, two lower branches.** $U = (-\infty,0)$ flows into $L_1, L_2 = (0,\infty)$, with conservation of flow $a_U\beta_U = a_{L_1}\beta_{L_1} + a_{L_2}\beta_{L_2}$ and Kirchhoff condition $a_{L_1}\partial_xw_{L_1}(t,0) + a_{L_2}\partial_xw_{L_2}(t,0) = a_U\partial_xw_U(t,0)$. Locally uniformly as $t\to\infty$: if $\beta_U < 2$, $w \to (1,1,1)$; if $\beta_U, \beta_{L_1}, \beta_{L_2} \ge 2$, $w \to (0,0,0)$ with $\|w_U\|_\infty \to 0$ and $\|w_{L_i}\|_\infty \to 1$; if $\beta_U \ge 2 > \min\{\beta_{L_1},\beta_{L_2}\}$, there is $\alpha_* \in (0,1)$ such that the steady-state problem has exactly one solution for each $\alpha \in [\alpha_*,1)$ and none for $\alpha < \alpha_*$, and $w$ converges to the solution with $\alpha = \alpha_*$, which is increasing in the flow direction.

In all three simple graphs (including the [two-branch river](two-branch-river-trichotomy.md)) the long-time behaviour is a trichotomy: persistence at carrying capacity, washing out, or persistence below carrying capacity, decided by comparing the branch flow speeds with the Fisher–KPP spreading speed $2$; the flow speeds themselves are tied to the graph topology and cross-sections by conservation of flow.

## Depends on

- [Fisher–KPP advection–diffusion on a two-branch river: steady states and trichotomy](two-branch-river-trichotomy.md)

## Expansion

The steady-state sets (Theorems 1.3 and 1.5) are richer than on two branches: continua of increasing solutions and solutions decreasing on one upper branch coexist. The long-time limit is still selected by upstream decay: compactly supported data are trapped between sub- and supersolutions built from steady states with the fastest decay at $-\infty$ on the upstream branches, so only the critical-$\alpha$ steady state can be the limit.

## Sources

- Yihong Du, Bendong Lou, Rui Peng and Maolin Zhou, "The Fisher-KPP equation over simple graphs: varied persistence states in river networks", Journal of Mathematical Biology (2020), <https://doi.org/10.1007/s00285-020-01474-1>. arXiv:1809.06961. Sections 1.2–1.4, Eqs. (1.11)–(1.21), Theorems 1.3–1.6 and Remark 1.7.
