# Line of equilibria of the two-community feedback game when the environmental ratios coincide

In the symmetric three-dimensional reduction of the [eco-evolutionary game with environmental feedback on two communities](two-community-eco-evolutionary-game-and-its-edge-equilibria.md), assume $\theta_1 = \theta_2 = \theta_{12}$ and write $\rho_1 = R_0 - R_1 - T_0 + T_1 - (P_0 - P_1 - S_0 + S_1)\theta_1$.

**Theorem.** All eight corner equilibria are saddles. The interior equilibria are exactly the points of the line segment

$$\mathcal{L}: \quad x^* = \frac{1}{1 + \theta_1}, \qquad n_1^*(1 - \delta) + n_{12}^*\delta = \frac{R_0 - T_0 - P_0\theta_1 + S_0\theta_1}{\rho_1},$$

with $n_1^*, n_{12}^* \in (0, 1)$. Along $\mathcal{L}$ the Jacobian has a zero eigenvalue in the direction of $\mathcal{L}$, and its other two eigenvalues have negative real part whenever the payoff conditions $R_0 > T_0$, $S_0 > P_0$, $R_1 < T_1$, $S_1 < P_1$ and $(P_0 - S_0)(R_1 - T_1) > (P_1 - S_1)(R_0 - T_0)$ hold. In that case $\mathcal{L}$ is a normally attracting line of neutrally stable equilibria, and in the paper's simulations nearby trajectories spiral into it.

Hence, when $\theta_1 = \theta_{12}$ the network structure does not enter the stability requirement, only the position of the attracting set through $\delta$; when $\theta_1 \ne \theta_{12}$ it does, through the windows $\delta_{c,1} < \delta < \delta_{c,2}$ or $\delta_{c,3} < \delta < \delta_{c,4}$.

## Depends on

- [Eco-evolutionary game with environmental feedback on two communities: model and stable edge equilibria](two-community-eco-evolutionary-game-and-its-edge-equilibria.md)

## Expansion

With $\theta_1 = \theta_{12}$ the two environmental equations vanish at the same $x^* = 1/(1 + \theta_1)$, so interior equilibria need only the payoff balance $\dot x = 0$ at that $x^*$. The $x$ equation depends on $(n_1, n_{12})$ only through $n_{\mathrm{eff}} = (1 - \delta)n_1 + \delta n_{12}$, so the balance fixes $n_{\mathrm{eff}}$ and leaves a one-parameter family. Moving along $\mathcal{L}$ changes nothing in the vector field to first order, which gives the zero eigenvalue. Appendix E computes the two remaining eigenvalues and shows their real parts are negative under the payoff conditions labelled (2) and (19) in the paper (the Nash inequalities and the cross-product inequality above); (19) is also the stability condition of the well-mixed feedback game of Weitz et al., recovered when $n_1 = n_{12}$. The two transverse eigenvalues are $\lambda_{2,3} = \tfrac12\big(\sigma_1 \pm \sqrt{\sigma_1^2 + 4(\sigma_2\sigma_4 + \sigma_3\sigma_5)}\big)$ (Eqs. (131)–(135)), where $\sigma_1, \sigma_2, \sigma_3$ are constant along $\mathcal L$ but $\sigma_4 = n_1^*(1 - n_1^*)(1 + \theta_1)$ and $\sigma_5 = n_{12}^*(1 - n_{12}^*)(1 + \theta_1)$ depend on the individual coordinates, not only on the combination fixed by Eq. (43). So the real part $\sigma_1/2$ is the same at every point of $\mathcal L$ while the imaginary parts vary. For the payoffs of Eq. (38), $\theta_1 = 5$ and $\delta = 0.5$, the line is $x^* = 1/6$, $(n_1^* + n_{12}^*)/2 = 7/22$; at $(n_1^*, n_{12}^*) = (7/22, 7/22)$ the transverse eigenvalues are $-0.019 \pm 0.814i$, and at $(1/11, 6/11)$ they are $-0.019 \pm 0.710i$. The source reports $-0.019 \pm 0.810i$ for this parameter set without naming the point of $\mathcal L$.

## Sources

- K. Betz, F. Fu and N. Masuda, Evolutionary game dynamics with environmental feedback in a network with two communities, *Bull. Math. Biol.* 86 (2024), article 84, <https://doi.org/10.1007/s11538-024-01310-3>, PMCID PMC11161456. Section 4, equations (42)-(43), Appendices D-E, Section 6.
