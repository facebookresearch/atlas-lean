# Backward bifurcation criterion for the SIR model with saturated incidence and saturated treatment

**Model.** With constant recruitment $A > 0$, natural death $d > 0$, disease death $\delta \ge 0$, natural recovery $\gamma \ge 0$, transmission rate $\beta > 0$, inhibitory factor $\alpha \ge 0$, cure rate $r > 0$, treatment-saturation parameter $b \ge 0$, and constant vaccination and treatment levels $u_1, u_2 \in [0,1]$, consider

$$
\begin{aligned}
\frac{dS}{dt} &= A - \frac{\beta SI}{1+\alpha I} - dS - u_1S, \\
\frac{dI}{dt} &= \frac{\beta SI}{1+\alpha I} - (d+\delta+\gamma)I - \frac{ru_2I}{1+bu_2I}, \\
\frac{dR}{dt} &= \frac{ru_2I}{1+bu_2I} + \gamma I + u_1S - dR.
\end{aligned}
$$

The maximal treatment supply per unit time is $r/b$. The region $\{S + I + R \le A/d\}$ is positively invariant, and the disease-free equilibrium is $A_1 = \left(\frac{A}{d+u_1}, 0, \frac{u_1A}{d(d+u_1)}\right)$. Write $D = d + \delta + \gamma$. The next-generation matrix gives

$$
R_0 = \frac{\beta A}{(d+u_1)(D + ru_2)}.
$$

**Endemic equilibria.** The infective level of an endemic equilibrium is a positive root of $C_1I^2 + C_2I + C_3 = 0$ with

$$
C_1 = bu_2D\{\beta + \alpha(d+u_1)\}, \quad C_2 = bu_2\{(d+u_1)D - \beta A\} + (D + ru_2)\{\beta + \alpha(d+u_1)\}, \quad C_3 = (d+u_1)(D+ru_2)(1 - R_0).
$$

So there is exactly one endemic equilibrium if $R_0 > 1$, none if $R_0 < 1$ and $C_2 > 0$, and two if $R_0 < 1$, $C_2 < 0$ and $C_2^2 > 4C_1C_3$.

**Theorem.**
1. $A_1$ is locally asymptotically stable if $R_0 < 1$ and unstable if $R_0 > 1$. If $R_0 < 1$ and $\alpha \ge bu_2$, $A_1$ is globally asymptotically stable.
2. If $\beta A > (d+u_1)D$, a transcritical bifurcation occurs at $A_1$ as the treatment level $u_2$ passes through $u_2^0 = \frac{\beta A}{r(d+u_1)} - \frac{D}{r}$.
3. The system has a **backward bifurcation** at $R_0 = 1$ if and only if

$$
(ru_2 + D)(ru_2 + D + \alpha A) < bru_2^2A.
$$

4. If $R_0 > 1$ and $\beta \ge \max\{rbu_2^2, r\alpha u_2\}$, the unique endemic equilibrium is locally asymptotically stable. If the backward-bifurcation condition holds, there is $R_0^* < 1$ such that for $R_0^* < R_0 < 1$ there are two endemic equilibria: the one with fewer infectives is unstable, and the one with more infectives is locally asymptotically stable when $\beta \ge \max\{rbu_2^2, r\alpha u_2\}$. It then coexists with the stable disease-free equilibrium.

Item 3 shows that a large treatment-saturation parameter $b$, meaning scarce treatment capacity, is what produces bistability. Without treatment saturation ($b = 0$) the bifurcation is always forward.

## Depends on

- [Next-generation matrix and the basic reproduction number](../../next-generation-matrix-and-the-basic-reproductio/README.md)
- [Global behaviour of the SIR model](../../global-behaviour-of-the-sir-model/README.md)

## Expansion

Substitute $\beta = R_0(d+u_1)(D+ru_2)/A$ into $C_1, C_2, C_3$, so that the endemic branch is a curve $I = I(R_0)$ through $(R_0, I) = (1, 0)$. Implicit differentiation of $C_1I^2 + C_2I + C_3 = 0$ at $(1,0)$ gives

$$
\left.\frac{\partial I}{\partial R_0}\right|_{R_0=1,\,I=0} = \frac{A(D + ru_2)}{(D+ru_2)(D+ru_2+\alpha A) - bru_2^2A}.
$$

The bifurcation is backward exactly when this slope is negative, which gives item 3. Local stability of the disease-free equilibrium follows from the sign of the single nontrivial eigenvalue $\beta A/(d+u_1) - (D + ru_2)$. At $R_0 = 1$ the Jacobian at $A_1$ has eigenvalues $0, -(d+u_1), -d$. The critical case is settled by reducing the flow to an invariant curve tangent to the centre eigendirection and reading off the sign of its quadratic coefficient, which decides stability of $A_1$ at $R_0 = 1$ (an explicit parameter inequality) and gives the transcritical bifurcation in $u_2$.

## Sources

- Jayanta Kumar Ghosh, Uttam Ghosh, M. H. A. Biswas and Susmita Sarkar, "Qualitative Analysis and Optimal Control Strategy of an SIR Model with Saturated Incidence and Treatment", arXiv:1807.05954 (2018), Section 3 (Lemmas 1–2, equilibrium quadratic), Section 4 (Theorems 1–4), Section 5 (Theorems 5–6), <https://doi.org/10.48550/arXiv.1807.05954>. Published version: Differential Equations and Dynamical Systems 31(1) (2023), 53–67, <https://doi.org/10.1007/s12591-019-00486-8>; locators above refer to the arXiv version.
