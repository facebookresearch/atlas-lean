# Existence and penalty approximation of drug-window-constrained tumor control

**Model.** Let $\Omega \subset \mathbb{R}^n$ be a bounded Lipschitz domain and $T > 0$. The normalized tumor-cell density $y(x,t)$ and the normalized tissue drug concentration $s(t)$, driven by the drug supply $u \in U = L^2(0,T)$, satisfy

$$y_t - \nabla\cdot(k\nabla y) = d(s)\, y, \quad y|_{\partial\Omega} = 0, \quad y(\cdot,0) = y_0; \qquad s'(t) + M_0 s(t) = u(t), \quad s(0) = 0,$$

with $M_0 > 0$ and the hypotheses

- (i) $0 < k_0 \le k(x) \le k_1$ and $y_0 \in L^2(\Omega)$;
- (ii) $d(s)(s - s_m) < 0$ for $s \ne s_m$ (net growth below the threshold concentration $s_m$, net kill above it), and $d$ is locally Lipschitz.

**Problem (P).** For $\lambda > 0$ minimize $J(y,u) = \tfrac12\|y\|^2_{L^2(\Omega\times(0,T))} + \tfrac{\lambda}{2}\|u\|^2_{L^2(0,T)}$ subject to the state equations and the **therapeutic window**

$$s(t) \le s_+ \ \text{ for } t \in (0,T), \qquad s(t) \ge s_- \ \text{ for } t \in (t_0, T).$$

**Theorem.**

1. *(Existence.)* Under (i)–(ii), if

$$\frac{1 - e^{-M_0 T}}{1 - e^{-M_0 t_0}}\, s_- \le s_+,$$

then Problem (P) has a solution.
2. *(Penalty problem.)* For $\varepsilon > 0$ replace the window constraints by the penalty $\varepsilon^{-1}\int_0^T (s - s_+)_+^2\, dt + \varepsilon^{-1}\int_{t_0}^T (s_- - s)_+^2\, dt$ added to $J$. This penalized problem $(P_\varepsilon)$ has a solution $(y_\varepsilon, s_\varepsilon, u_\varepsilon)$, and along a sequence $\varepsilon \to 0^+$, $u_\varepsilon \rightharpoonup \hat u$ weakly in $L^2(0,T)$, $y_\varepsilon \to \hat y$ strongly in $L^2(0,T; L^2(\Omega))$ and $s_\varepsilon \to \hat s$ strongly in $L^2(0,T)$, where $(\hat y, \hat u)$ solves (P).
3. *(Optimality system.)* Each solution of $(P_\varepsilon)$ has a unique adjoint pair $(p_1, p_2)$ with $p_1(T) = 0$, $p_2(T) = 0$,

$$-p_1' + A p_1 - d(s_\varepsilon) p_1 = -y_\varepsilon, \qquad -p_2' + M_0 p_2 + \tfrac{1}{\varepsilon}\, f_1'(s_\varepsilon) + \tfrac{1}{\varepsilon}\,\chi(s_\varepsilon, t) = d'(s_\varepsilon)\,(y_\varepsilon, p_1),$$

where $A = -\nabla\cdot(k\nabla\,\cdot)$ with Dirichlet conditions, $f_1(s) = (s - s_+)_+^2$, $\chi(s,t) = \frac{d}{ds}(s_- - s)_+^2$ for $t \ge t_0$ and $0$ otherwise; the optimal supply is $u_\varepsilon = \lambda^{-1} p_2$.

## Depends on

- [Concentration in the one-compartment model](../../../pharmacokinetics/one-compartment-linear-pharmacokinetics/concentration.md)

## Expansion

The concentration is $s(t) = \int_0^t e^{-M_0(t-\tau)} u(\tau)\, d\tau$, so $|s(t)| \le \sqrt t\,\|u\|_{L^2}$ and $\|s'\|_{L^2} \le (1 + M_0 T)\|u\|_{L^2}$. A constant infusion $u \equiv M_0 s_-/(1 - e^{-M_0 t_0})$ reaches $s_-$ exactly at $t_0$ and stays below $s_-(1 - e^{-M_0 T})/(1 - e^{-M_0 t_0})$; the compatibility condition says this stays under the ceiling, so the admissible set is nonempty. Energy estimates for the linear parabolic equation with bounded coefficient $d(s)$ give a unique weak solution, a minimizing sequence is bounded in $L^2$, and Aubin–Lions compactness passes to the limit in the bilinear term $d(s)y$; weak lower semicontinuity of $J$ gives a minimizer. The penalty problem is unconstrained, so the same argument gives existence; letting $\varepsilon \to 0$ forces the penalty terms to vanish. Surjectivity of the linearized constraint operator yields Lagrange multipliers, which are the adjoint states.

## Sources

- Andrey Kovtanyuk, Christina Kuttler, Kristina Koshel, Alexander Chebotarev, "Inverse Extremal Problem for an Anti-Tumor Therapy Model", in 2024 Days on Diffraction (DD) (2024), 90–95, <https://doi.org/10.1109/dd62861.2024.10767971>. Published version of arXiv:2407.08345, cited next; locators there refer to the arXiv version.
- Andrey Kovtanyuk, Christina Kuttler, Kristina Koshel, Alexander Chebotarev, "Inverse extremal problem for an anti-tumor therapy model", arXiv (2024). Section 2 (model and Problem (P)), Lemmas 1–3, Theorems 1–4. <https://doi.org/10.48550/arXiv.2407.08345>
