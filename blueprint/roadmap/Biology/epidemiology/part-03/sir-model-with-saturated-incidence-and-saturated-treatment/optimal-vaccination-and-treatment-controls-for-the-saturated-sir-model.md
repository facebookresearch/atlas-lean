# Optimal vaccination and treatment controls for the saturated SIR model

**Problem.** In the SIR model with saturated incidence and saturated treatment

$$
\dot S = A - \frac{\beta SI}{1+\alpha I} - dS - u_1S, \qquad \dot I = \frac{\beta SI}{1+\alpha I} - (d+\delta+\gamma)I - \frac{ru_2I}{1+bu_2I}, \qquad \dot R = \frac{ru_2I}{1+bu_2I} + \gamma I + u_1S - dR,
$$

let the vaccination rate $u_1(t)$ and the treatment effort $u_2(t)$ range over the admissible set $U$ of Lebesgue-measurable controls with $0 \le u_1, u_2 \le 1$ on $[0, T]$. Minimise

$$
J(u_1, u_2) = \int_0^T\left(A_1S + A_2I + B_1u_1^2 + B_2u_2^2\right)dt,
$$

where $A_1, A_2 > 0$ weight the burden of susceptibles and infectives and $B_1, B_2 > 0$ are the costs of vaccination and treatment.

**Theorem.**
1. An optimal pair $(u_1^*, u_2^*) \in U$ exists.
2. Let $\lambda_1, \lambda_2, \lambda_3$ solve the adjoint system

$$
\begin{aligned}
\dot\lambda_1 &= -A_1 + \frac{(\lambda_1-\lambda_2)\beta I}{1+\alpha I} + d\lambda_1 + u_1(\lambda_1 - \lambda_3), \\
\dot\lambda_2 &= -A_2 + \frac{(\lambda_1-\lambda_2)\beta S}{(1+\alpha I)^2} + \frac{(\lambda_2-\lambda_3)ru_2}{(1+bu_2I)^2} + (d+\delta)\lambda_2 + \gamma(\lambda_2-\lambda_3), \\
\dot\lambda_3 &= d\lambda_3,
\end{aligned}
$$

with $\lambda_i(T) = 0$, evaluated along the optimal state $(S^*, I^*, R^*)$. Then

$$
u_1^* = \max\left\{0, \min\left\{\frac{(\lambda_1 - \lambda_3)S^*}{2B_1}, 1\right\}\right\}, \qquad u_2^* = \max\{0, \min\{\bar u_2, 1\}\},
$$

where $\bar u_2$ is the nonnegative root of $u_2(1 + bu_2I^*)^2 = \frac{(\lambda_2 - \lambda_3)rI^*}{2B_2}$.

Because the treatment term saturates, the treatment control is not a linear projection of the switching function. It solves a cubic, and its effect falls off as the infective load grows.

## Depends on

- [Backward bifurcation criterion for the SIR model with saturated incidence and saturated treatment](backward-bifurcation-criterion-for-the-sir-model-with-saturated-incidence-and-treatment.md)

## Expansion

Existence follows from the convexity of the integrand in $(u_1, u_2)$, the convexity and compactness of the control set, and the boundedness and Lipschitz continuity of the state system on the invariant region $\{S+I+R \le A/d\}$. Pontryagin's maximum principle uses the Hamiltonian $H = A_1S + A_2I + B_1u_1^2 + B_2u_2^2 + \lambda_1\dot S + \lambda_2\dot I + \lambda_3\dot R$. The adjoint equations are $\dot\lambda_i = -\partial H/\partial x_i$, with transversality $\lambda_i(T) = 0$. The stationarity conditions $\partial H/\partial u_1 = 0$ and $\partial H/\partial u_2 = 0$ give $u_1 = (\lambda_1 - \lambda_3)S/(2B_1)$ and $u_2(1+bu_2I)^2 = (\lambda_2-\lambda_3)rI/(2B_2)$. Since $H$ is strictly convex in $(u_1, u_2)$, projecting onto $[0,1]$ gives the minimiser.

## Sources

- Jayanta Kumar Ghosh, Uttam Ghosh, M. H. A. Biswas and Susmita Sarkar, "Qualitative Analysis and Optimal Control Strategy of an SIR Model with Saturated Incidence and Treatment", arXiv:1807.05954 (2018), Section 6 (objective functional, Theorems 7–8, adjoint system), <https://doi.org/10.48550/arXiv.1807.05954>. Published version: Differential Equations and Dynamical Systems 31(1) (2023), 53–67, <https://doi.org/10.1007/s12591-019-00486-8>; locators above refer to the arXiv version.
