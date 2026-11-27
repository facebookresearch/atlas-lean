# Fixed points and stability of health in the antigenicity HIV model

**Setting.** Consider the single-antigenicity, dimensionless HIV model with healthy lymphocytes $T$, infected lymphocytes $U$, infectious virions $V$ and non-infectious virions $W$:

$$\frac{dT}{dt} = \beta(1 - T) - \frac{T}{\tau} J\Big(\frac{V}{T}\Big) + \omega (V + W) T, \qquad \frac{dU}{dt} = \frac{T}{\tau} J\Big(\frac{V}{T}\Big) - \alpha U,$$

$$\frac{dV}{dt} = a\theta U - \zeta V T, \qquad \frac{dW}{dt} = a(1-\theta) U - \zeta W T,$$

with positive parameters, $0 < \theta < 1$, and a concave saturating infection function $J$ with $J(0) = 0$, $J'(0) = 1$, $J(\infty) = 1$. Define

$$\eta = a\omega - \alpha\zeta, \qquad \rho = \frac{\alpha\zeta\tau}{a\theta}, \qquad \overline{V} = \frac{\beta a\theta}{a\omega - \alpha\zeta}.$$

The state $(T, U, V, W) = (1, 0, 0, 0)$ is called **health**; a fixed point with $V > 0$ is called **seropositivity**.

**Proposition (fixed points).**

- If $\eta > 0$: the fixed points are health and one seropositivity state when $\rho < 1$, and health only when $\rho \ge 1$.
- If $\eta = 0$: health is the only fixed point.
- If $\eta < 0$: health is always a fixed point, and there is a threshold $L > 1$ (not explicit) such that there is one seropositivity fixed point when $\rho < 1$, two when $1 < \rho < L$, and none when $\rho > L$.

**Theorem (stability of health).** If $\rho > 1$, health is locally asymptotically stable. If $\rho < 1$, the linearization at health has exactly one positive eigenvalue, and its eigenvector is admissible (pointing into the non-negative orthant), so health is unstable along a biologically meaningful direction.

Thus $1/\rho = a\theta/(\alpha\zeta\tau)$ plays the role of a basic reproduction number: it is the number of infectious virions produced per virion over one infection cycle at the healthy lymphocyte level.

## Depends on

- [Biological consistency and global existence of the antigenicity HIV model](biological-consistency-and-global-existence-of-the-antigenicity-hiv-model.md)

## Expansion

At a fixed point, $(1-\theta)V = \theta W$ and $U = \zeta V T/(a\theta)$. Eliminating gives $T = 1/(1 - V/\overline{V})$ and the scalar equation

$$J\Big(V\,\frac{\overline{V} - V}{\overline{V}}\Big) = \rho V.$$

For $\eta > 0$ the left side is a concave hump symmetric about $\overline{V}/2$ with slope $1$ at $V = 0$, so a positive root exists exactly when the line $\rho V$ starts below it, i.e. $\rho < 1$. For $\eta < 0$ one inverts $X = V(1 - V/\overline{V})$ on $[0,\infty)$ and compares $J(X)$ with $\rho\psi(X)$, which can cross zero, one or two times. At health the characteristic polynomial factors as

$$P(\lambda) = (\zeta + \lambda)(\beta + \lambda)\Big(\frac{a\theta}{\tau}(\rho - 1) + (\alpha + \zeta)\lambda + \lambda^2\Big),$$

whose quadratic factor has positive discriminant $(\alpha - \zeta)^2 + 4a\theta/\tau$; its constant term changes sign at $\rho = 1$.

## Sources

- F. Dubois, H. V. J. Le Meur and C. Reiss, "Mathematical modeling of antigenicity for HIV dynamics", MathS In Action 3 (2010), no. 1, 1–35; arXiv:0810.2988: Proposition 14 (fixed points, Section 4-3) and Theorem 15 (stability of the health state, Section 4-4-1). <https://doi.org/10.48550/arXiv.0810.2988>. Published version: MathematicS In Action 3(1) (2010), 1–35, <https://doi.org/10.5802/msia.3>; locators above refer to the arXiv version.
