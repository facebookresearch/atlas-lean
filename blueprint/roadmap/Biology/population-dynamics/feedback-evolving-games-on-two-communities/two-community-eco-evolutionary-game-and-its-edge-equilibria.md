# Eco-evolutionary game with environmental feedback on two communities: model and stable edge equilibria

An infinite population is split into two equal communities; players meet others in their own community at rate $1 - \delta$ and in the other community at rate $\delta \in (0, 1)$. Each edge type carries an environmental state $n_1, n_2, n_{12} \in [0, 1]$ (within community 1, within community 2, between communities), and the payoff matrix depends linearly on it:

$$A(n) = (1 - n)\begin{pmatrix} R_0 & S_0 \\ T_0 & P_0 \end{pmatrix} + n \begin{pmatrix} R_1 & S_1 \\ T_1 & P_1 \end{pmatrix}, \qquad R_0 > T_0,\ S_0 > P_0,\ R_1 < T_1,\ S_1 < P_1,$$

so cooperation is the unique Nash equilibrium in the replete state $n = 0$ and defection in the depleted state $n = 1$. With $x, y$ the fractions of cooperators in communities 1 and 2, $\mathbf{x} = (x, 1 - x)^T$, $\mathbf{y} = (y, 1 - y)^T$, the payoff vectors are $q_1 = (1 - \delta)A(n_1)\mathbf{x} + \delta A(n_{12})\mathbf{y}$ and $q_2 = (1 - \delta)A(n_2)\mathbf{y} + \delta A(n_{12})\mathbf{x}$, and

$$\dot x = x(1 - x)(q_{11} - q_{12}), \quad \dot y = y(1 - y)(q_{21} - q_{22}),$$

$$\dot n_1 = n_1(1 - n_1)[\theta_1 x - (1 - x)], \quad \dot n_2 = n_2(1 - n_2)[\theta_2 y - (1 - y)], \quad \dot n_{12} = n_{12}(1 - n_{12})[\theta_{12} z - (1 - z)],$$

with $z = (x + y)/2$ and enhancement-to-degradation ratios $\theta_1, \theta_2, \theta_{12} > 0$.

**Symmetric reduction.** If $\theta_1 = \theta_2$ and the initial data satisfy $x = y$, $n_1 = n_2$, these identities persist, and the system reduces to

$$\dot x = x(1 - x)\Big[(R_0 - T_0 - S_0 + P_0)x + S_0 - P_0 - \big[n_1(1 - \delta) + \delta n_{12}\big]\big[(R_3 - S_3 - T_3 + P_3)x + S_3 - P_3\big]\Big],$$

$$\dot n_1 = n_1(1 - n_1)[\theta_1 x - (1 - x)], \qquad \dot n_{12} = n_{12}(1 - n_{12})[\theta_{12} x - (1 - x)],$$

where $R_3 = R_0 - R_1$, $S_3 = S_0 - S_1$, $T_3 = T_0 - T_1$, $P_3 = P_0 - P_1$, on the unit cube.

**Theorem (case $\theta_1 \ne \theta_{12}$).** All eight corner equilibria are saddles and there is no interior equilibrium. Let $\gamma = R_3 - T_3 - S_3 + P_3$, $\rho_1 = R_3 - T_3 - (P_3 - S_3)\theta_1$, $\rho_{12} = R_3 - T_3 - (P_3 - S_3)\theta_{12}$, $\delta_{c,1} = (R_0 - T_0 - (P_0 - S_0)\theta_1)/\rho_1$ and $\delta_{c,2} = (R_0 - T_0 - (P_0 - S_0)\theta_{12})/\rho_{12}$. The edge equilibrium

$$(x^*, n_1^*, n_{12}^*) = \Big(\frac{P_0 - S_0 - \delta(P_0 - P_1 - S_0 + S_1)}{R_0 - T_0 - S_0 + P_0 - \delta\gamma},\ 0,\ 1\Big)$$

is stable if and only if

$$(P_0 - S_0)(R_1 - T_1) > (P_1 - S_1)(R_0 - T_0), \qquad \delta_{c,1} < \delta < \delta_{c,2}, \qquad \theta_{12} > \theta_1.$$

Symmetrically, with $\delta_{c,3} = (-R_1 + T_1 + (P_1 - S_1)\theta_1)/\rho_1$ and $\delta_{c,4} = (-R_1 + T_1 + (P_1 - S_1)\theta_{12})/\rho_{12}$, the edge equilibrium $\big((P_1 - S_1 + \delta(P_0 - P_1 - S_0 + S_1))/(R_1 - T_1 - S_1 + P_1 + \delta\gamma),\ 1,\ 0\big)$ is stable if and only if the same first inequality holds, $\delta_{c,3} < \delta < \delta_{c,4}$ and $\theta_{12} < \theta_1$. Outside these windows a face equilibrium is stable, and stability passes between face and edge equilibria through transcritical bifurcations at the critical values of $\delta$.

## Depends on

- [Solution of the replicator equation](../replicator-dynamics/is-solution.md)

## Expansion

Since $A(n)$ is affine in $n$, a player in community 1 effectively faces the environment $n_{\mathrm{eff}} = (1 - \delta)n_1 + \delta n_{12}$, which gives the reduced $x$ equation. An interior equilibrium would need $x^* = 1/(1 + \theta_1)$ from $\dot n_1 = 0$ and $x^* = 1/(1 + \theta_{12})$ from $\dot n_{12} = 0$, impossible when $\theta_1 \ne \theta_{12}$. At an edge $x^* \in (0, 1)$ forces $(n_1, n_{12}) \in \{(0, 1), (1, 0)\}$, since the other two pairs make $A(n_{\mathrm{eff}})$ a pure cooperation or pure defection game; then $x^*$ is the mixed equilibrium of $A(\delta)$ or $A(1 - \delta)$. The Jacobian at the edge point is block triangular; the $n_1$ and $n_{12}$ directions are stable exactly when $\theta_1 x^* - (1 - x^*) < 0 < \theta_{12} x^* - (1 - x^*)$, i.e. $1/(1 + \theta_{12}) < x^* < 1/(1 + \theta_1)$, which requires $\theta_{12} > \theta_1$ and, as $x^*$ moves with $\delta$, becomes the window $\delta_{c,1} < \delta < \delta_{c,2}$. Appendix B combines these with the eigenvalue $x^*(1 - x^*)\,\partial_x(q_{11} - q_{12})$ in the $x$ direction to obtain the first inequality, which is the stability condition of the well-mixed feedback game of Weitz et al.

## Sources

- K. Betz, F. Fu and N. Masuda, Evolutionary game dynamics with environmental feedback in a network with two communities, *Bull. Math. Biol.* 86 (2024), article 84, <https://doi.org/10.1007/s11538-024-01310-3>, PMCID PMC11161456. Section 2, equations (1)-(15); Section 3, equations (18)-(29), Section 3.5; Appendices A-B.
- J. S. Weitz, C. Eksin, K. Paarporn, S. P. Brown and W. C. Ratcliff, An oscillating tragedy of the commons in replicator dynamics with game-environment feedback, *Proc. Natl. Acad. Sci. USA* 113 (2016), E7518-E7525, <https://doi.org/10.1073/pnas.1604096113>.
