# Fundamental bifurcation theorem for nonlinear matrix models

**Setting.** A population distribution $x \in \mathbb R^n_+$ evolves by $x' = r\,P(x)\,x$, where (A1) the entries $p_{ij}(x)$ are non-negative and twice continuously differentiable on an open set containing $\mathbb R^n_+$, $P(x)$ is primitive, and $P$ is normalized so that $\rho[P(0)] = 1$. Then $r$ is the spectral radius of the linearization at extinction, the **inherent population growth rate**. An **equilibrium pair** $(r,x)$ solves $x = rP(x)x$; it is positive if $x \in \mathbb R^n_+ \setminus\{0\}$. Let $v > 0$ and $w > 0$ be right and left eigenvectors of $P(0)$ for the eigenvalue $1$, and

$$\kappa = -\sum_{i,j} w_i\,v_j\,\big(\nabla_x p_{ij}(0)\cdot v\big).$$

**Theorem.**
1. *(Global continuum.)* Under A1 there is an unbounded continuum $\mathcal C^+$ of positive equilibrium pairs that bifurcates from $(r,x) = (1,0)$.
2. *(Direction and stability.)* Near $(1,0)$: if $\kappa < 0$ the bifurcation is backward (positive equilibria exist for $r < 1$) and those equilibria are unstable; if $\kappa > 0$ it is forward ($r > 1$) and they are locally asymptotically stable. The extinction equilibrium is stable for $r < 1$ and unstable for $r > 1$.
3. *(Net reproductive number.)* If $P(x) = F(x) + T(x)$ with fecundity matrix $F \ge 0$ and transition matrix $T \ge 0$ with $\rho[T(0)] < 1$, the inherent net reproductive number $R_0 = \rho\big[F(0)(I - T(0))^{-1}\big]$ satisfies $R_0 < 1$, $= 1$, $> 1$ exactly when $r < 1$, $= 1$, $> 1$, and $R_0$ may replace $r$ as the bifurcation parameter in parts 1–2.

## Depends on

- [Perron–Frobenius theorem for primitive nonnegative matrices](../../../../LinearAlgebra/special-matrices/perron-frobenius-theorem/perron-frobenius-for-primitive-nonnegative-matri.md)

## Expansion

Writing the equilibrium equation as $x = rP(0)x + h(r,x)$ with $h$ of higher order, the Rabinowitz global bifurcation alternative applies at the simple characteristic value $r = 1$ (simple and with positive eigenvector by Perron–Frobenius); positivity rules out the alternative of returning to another characteristic value, leaving an unbounded branch. A Lyapunov–Schmidt expansion $x = \varepsilon v + O(\varepsilon^2)$, $r = 1 + r_1\varepsilon + O(\varepsilon^2)$ gives $r_1 = \kappa/(w^{\mathsf T}v)$, so the sign of $\kappa$ fixes the direction, and the exchange of stability links direction to stability. If every derivative $\partial p_{ij}/\partial x_k(0) \le 0$ (negative density feedback only) and not all vanish, then $\kappa > 0$; a backward bifurcation requires at least one positive derivative, a component Allee effect.

## Sources

- J. M. Cushing, "Backward bifurcations and strong Allee effects in matrix models for the dynamics of structured populations", Journal of Biological Dynamics 8(1) (2014) 57–73, Section 2, assumption A1, Theorems 1–2, Notes 1 and 5, <https://doi.org/10.1080/17513758.2014.899638>, PMCID PMC4241602.
