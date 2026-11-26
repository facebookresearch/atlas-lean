# Central equilibrium and decay-driven instability in a sigmoidal gene regulatory network

**Model.** Three genes with expression levels $x_i \ge 0$ interact through a regulatory matrix $W = (w_{ij})$ (positive entries activate, negative entries repress) and decay at rates $v_i > 0$:

$$x_i' = \frac{1}{1 + e^{-\mu_i\left(\sum_j w_{ij}x_j - \theta_i\right)}} - v_ix_i, \qquad i = 1,2,3,$$

with sigmoid steepness $\mu_i > 0$ and thresholds $\theta_i$.

**Proposition (trapping box and central equilibrium).** The box $Q_3 = \{0 < x_i < 1/v_i\}$ is forward invariant and contains every equilibrium. Its center $(0.5/v_1, 0.5/v_2, 0.5/v_3)$ is an equilibrium iff

$$\theta_i = \sum_j w_{ij}\,\frac{0.5}{v_j}, \qquad i = 1,2,3,$$

i.e. each sigmoid is exactly at its midpoint there. At this point the Jacobian is

$$J = \Big(\frac{\mu_i}{4}w_{ij}\Big)_{i,j} - \operatorname{diag}(v_1, v_2, v_3),$$

since the logistic sigmoid has slope $\mu_i/4$ at its midpoint.

**Instability criteria.** With $S = v_1 + v_2 + v_3$, $P = v_1v_2 + v_1v_3 + v_2v_3$, $Q = v_1v_2v_3$ and $\mu_i = 4$, the cyclic network $w_{ii} = 1$, $w_{13} = w_{21} = w_{32} = -1$, other entries $0$, has characteristic polynomial

$$\lambda^3 + (S-3)\lambda^2 + (P - 2S + 3)\lambda + (Q - P + S) = 0 .$$

The central equilibrium is a saddle-focus with one positive real eigenvalue and a complex pair with negative real part when the cubic discriminant is negative, $a_0 = Q - P + S < 0$, and the real root exceeds $3 - S$ (here $a_2 = S - 3$, $a_1 = P - 2S + 3$, $a_0 = Q - P + S$). For the all-to-all activating network ($w_{ii} = 0$, $w_{ij} = 1$ for $i \ne j$) the polynomial is $\lambda^3 + S\lambda^2 + (P-3)\lambda + (Q - S - 2)$ with the analogous conditions. Thus the decay rates alone, through the symmetric functions $S, P, Q$, can switch the central state between stable and unstable regimes, change the number of equilibria, and create or destroy limit cycles.

## Depends on

## Expansion

Each right-hand side is positive at $x_i = 0$ and negative at $x_i = 1/v_i$ (the sigmoid lies in $(0,1)$), so the box traps trajectories and equilibria satisfy $v_ix_i \in (0,1)$. Choosing thresholds that center every sigmoid makes the center an equilibrium for any steepness. Linearization and the characteristic polynomial $\det(J - \lambda I)$ expand into coefficients that depend on the decay rates only through $S$, $P$, $Q$ when the regulatory pattern is fixed; the sign of the cubic discriminant decides between three real roots and one real root with a complex pair, and the sign of the constant term $-\det J$ decides whether an odd number of eigenvalues is positive.

## Sources

- O. Pokutnyi and F. Sadyrbaev, "The influence of decay in dynamic models of gene regulatory networks", arXiv:2610.18261 (2026), Section 2, Proposition 6.1 and the section "Conditions for instability", <https://doi.org/10.48550/arXiv.2610.18261>.
