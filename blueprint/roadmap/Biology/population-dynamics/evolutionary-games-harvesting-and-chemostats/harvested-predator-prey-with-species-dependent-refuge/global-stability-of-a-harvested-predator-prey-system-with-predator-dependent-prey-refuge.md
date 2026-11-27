# Global stability of a harvested predator–prey system with predator-dependent prey refuge

**Model.** Prey $x$ and predators $y$ with logistic prey growth (rate $r$, carrying capacity $k$), a refuge that shelters the fraction $my$ of prey (so $(1 - my)x$ prey are exposed, for $my < 1$), Holling type II predation with attack rate $p$ and handling parameter $a$, conversion efficiency $e$, predator death rate $d$, catchabilities $q_1, q_2$ and harvesting efforts $E_1, E_2$:

$$\frac{dx}{dt} = rx\Big(1 - \frac{x}{k}\Big) - \frac{p(1 - my)xy}{1 + ax(1 - my)} - q_1E_1x, \qquad \frac{dy}{dt} = \frac{ep(1 - my)xy}{1 + ax(1 - my)} - dy - q_2E_2y.$$

**Results.**

1. *(Boundedness.)* All solutions starting in the positive quadrant are uniformly bounded.
2. *(Global stability.)* An interior equilibrium $E^* = (x^*, y^*)$ is globally asymptotically stable in the positive quadrant if

$$4\,r\,m\,e\,(1 + ak)(1 + ax^*) > p\,m^2\,y^{*2}.$$

3. *(Bionomic equilibria.)* With prices $p_1, p_2$ and costs per unit effort $c_1, c_2$, the net revenue is $(p_1q_1x - c_1)E_1 + (p_2q_2y - c_2)E_2$; at a bionomic equilibrium with both fisheries operating, $x_\infty = c_1/(p_1q_1)$ and $y_\infty = c_2/(p_2q_2)$, and a fishery closes when its cost exceeds its revenue at the biological equilibrium.
4. *(Optimal harvesting.)* For the discounted revenue $\int_0^\infty e^{-\delta t}\,[(p_1q_1x - c_1)E_1 + (p_2q_2y - c_2)E_2]\,dt$, singular (interior) optimal efforts satisfy constant shadow prices $e^{\delta t}\lambda_1 = p_1 - c_1/(q_1x)$, $e^{\delta t}\lambda_2 = p_2 - c_2/(q_2y)$: the user cost per unit effort equals the discounted future marginal profit of effort at the optimal steady state.

## Depends on

- [Positive solutions lie on level curves](../../lotka-volterra-predator-prey-model/first-integral-eq.md)

## Expansion

Boundedness follows by combining the prey logistic bound with $e x + y$, whose derivative is bounded by a constant minus a multiple of itself. Global stability is obtained with a Lyapunov function of Volterra type, $V = (x - x^* - x^*\ln\frac{x}{x^*}) + (y - y^* - y^*\ln\frac{y}{y^*})$; its derivative is a quadratic form in $(x - x^*, y - y^*)$, and the stated inequality is the condition under which that form is definite, so $V$ decreases along all trajectories except at $E^*$. Because the refuge term $1 - my$ weakens predation exactly when predators are abundant, increasing $m$ damps the predator–prey oscillation; numerically, the refuge coefficient can remove the limit cycle and stabilize the coexistence state. The optimal-harvesting conditions are Pontryagin's maximum principle with controls entering linearly (singular arcs).

## Sources

- Md. Manarul Haque, Sahabuddin Sarwardi, "Dynamics of a Harvested Prey–Predator Model with Prey Refuge Dependent on Both Species", International Journal of Bifurcation and Chaos 28 (2018), 1830040, <https://doi.org/10.1142/s0218127418300409>. Published version of arXiv:1703.09275, cited next; locators there refer to the arXiv version.
- Md. Manarul Haque, Sahabuddin Sarwardi, "Dynamics of a harvested prey-predator model with prey refuge depended on both species", arXiv (2017). Proposition 1, Theorem 1, Section 6 (bionomic equilibrium), Section 7 (optimal harvesting policy). <https://doi.org/10.48550/arXiv.1703.09275>
