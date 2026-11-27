# Nash equilibria of two-type social distancing games with a cost-variance constraint

**Model.** A continuum of agents of two types, non-vulnerable ($j = 1$, mass $n_1$) and vulnerable ($j = 2$, mass $n_2$), each chooses a constant activity level $u \in [u_m, u_M]$ (fraction of time in public) for an epidemic wave $[0, T]$. With $\mu_j$ the distribution of actions of type $j$, the infection probabilities of an agent of type $j$ playing $u$ follow

$$
\dot S_{ju} = -r u S_{ju} I^f, \qquad \dot I_{ju} = r u S_{ju} I^f - \alpha_j I_{ju}, \qquad I^f(t) = \sum_{j=1}^2 \int u'\, I_{ju'}(t)\, \mu_j(du'),
$$

with $S_{ju}(0) = 1 - I_0$, $I_{ju}(0) = I_0$; this system has a unique solution, continuous in $u$. Writing $F(\mu_1, \mu_2) = r \int_0^T I^f(t)\,dt$, an agent of type $j$ playing $u$ pays

$$
J_j(u, \mu_1, \mu_2) = G_j\Big[I_0 + (1 - I_0)\big(1 - e^{-u F}\big)\Big] - s_{j1} u \bar u_1 - s_{j2} u \bar u_2,
$$

where $G_2 > G_1$ is the expected severity of infection, $\bar u_l$ the mean action of type $l$, and $s_{jl} \ge 0$ the social benefit of interaction.

**Theorem (unconstrained equilibria).** $J_j$ is concave in $u$, so best responses are $u_m$ or $u_M$. Let a fraction $\tilde u_j$ of type $j$ play $u_M$ and $1 - \tilde u_j$ play $u_m$, so $\bar u_j = u_m + (u_M - u_m)\tilde u_j$, and put $\Delta_j = G_j (1 - I_0)\big(e^{-u_m F} - e^{-u_M F}\big) - (u_M - u_m)(s_{j1}\bar u_1 + s_{j2}\bar u_2)$ with $F = F(\tilde u_1, \tilde u_2)$. Then $(\tilde u_1, \tilde u_2)$ is a Nash equilibrium iff for each $j$: $\Delta_j = 0$ if $0 < \tilde u_j < 1$; $\Delta_j \ge 0$ if $\tilde u_j = 0$; $\Delta_j \le 0$ if $\tilde u_j = 1$. If both types value interaction equally ($s_{11} = s_{21}$, $s_{12} = s_{22}$), every equilibrium has one of the forms $(0,0)$, $(\tilde u_1, 0)$, $(1, 0)$, $(1, \tilde u_2)$, $(1,1)$: the vulnerable never go out more than the non-vulnerable. If $u_m = 0$, $(0,0)$ is always an equilibrium.

**Theorem (equity-constrained equilibria).** Impose a shared bound $V(\mu_1, \mu_2) \le C$ on the population variance of costs. Define a generalized Nash equilibrium (GNE) through deviations of a vanishing mass $\varepsilon$ of type-$j$ players to a mixed strategy $\bar\mu'_j$: the cost change is $\mathcal{K}^j \delta\mu_j = \int J_j(u', \mu_1, \mu_2)\,\delta\mu_j(du')$ and the variance change is a bounded linear functional $\mathcal{L}^j \delta\mu_j$, with $\delta\mu_j = \bar\mu'_j - \bar\mu_j$. For a pair that is not variance-stationary, $(\mu_1, \mu_2)$ is a GNE iff either it is an unconstrained equilibrium with $V < C$ (Definition 1(i)) or $V = C$ and every cost-reducing deviation ($\mathcal{K}^j \delta\mu_j < 0$) does not reduce the variance budget violation ($\mathcal{L}^j \delta\mu_j \ge 0$). For pairs on the constraint boundary it suffices to test deviations supported on at most two points: with $g^{\mathcal K}_j(u)=\mathcal K^j(\delta_u-\bar\mu_j)$ and $g^{\mathcal L}_j(u)=\mathcal L^j(\delta_u-\bar\mu_j)$, a non-variance-stationary pair with $V = C$ is a GNE iff for all $u', u'' \in [u_m, u_M]$, $\rho \in [0,1]$ and $j$, $\rho g^{\mathcal K}_j(u') + (1-\rho) g^{\mathcal K}_j(u'') < 0$ implies $\rho g^{\mathcal L}_j(u') + (1-\rho) g^{\mathcal L}_j(u'') \ge 0$.

## Expansion

Concavity follows from $\partial_u^2 J_j = -G_j(1 - I_0) F^2 e^{-uF} < 0$, and the conditions on $\Delta_j = J_j(u_m) - J_j(u_M)$ say that mixing types are indifferent and pure types weakly prefer their action. In the variance-constrained game an individual cannot affect the variance, so equilibrium is defined through small-group deviations and Gateaux derivatives; the variance derivative is computed from the linearized epidemic system along $\delta\mu_j$, and the two-point reduction holds because the deviation test involves only two linear functionals of $\delta\mu_j$. In the source's numerical study, tightening $C$ lowers the cost of the vulnerable monotonically, can also improve the cost of the non-vulnerable relative to the unconstrained game, and slows the epidemic and lowers its prevalence.

## Sources

- I. Kordonis, A.-R. Lagos, G. P. Papavassilopoulos, "Nash Social Distancing Games with Equity Constraints: How Inequality Aversion Affects the Spread of Epidemics", arXiv:2009.00146 (2020): Section 2 (model, Proposition 1, cost and its concavity), Section 3 (Proposition 2 and its two corollaries), Section 4 (variance-constrained game, the two lemmas, Proposition 3, Corollaries 3–4), Appendices (proofs, linearization lemma). <https://doi.org/10.48550/arXiv.2009.00146> Published version: Applied Mathematics and Computation 434 (2022) 127453, <https://doi.org/10.1016/j.amc.2022.127453>.
