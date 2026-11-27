# Boundedness, bionomic equilibria and optimal harvesting of a predator–prey system with predator-dependent prey refuge

**Model.** Prey $x$ and predators $y$ with logistic prey growth (rate $r$, carrying capacity $k$), a refuge that shelters the fraction $my$ of prey (so $(1 - my)x$ prey are exposed, for $my < 1$), Holling type II predation with attack rate $p$ and handling parameter $a$, conversion efficiency $e$, predator death rate $d$, catchabilities $q_1, q_2$ and harvesting efforts $E_1, E_2$:

$$\frac{dx}{dt} = rx\Big(1 - \frac{x}{k}\Big) - \frac{p(1 - my)xy}{1 + ax(1 - my)} - q_1E_1x, \qquad \frac{dy}{dt} = \frac{ep(1 - my)xy}{1 + ax(1 - my)} - dy - q_2E_2y.$$

**Results.**

1. *(Boundedness.)* All solutions starting in the positive quadrant are uniformly bounded.
2. *(Bionomic equilibria.)* With prices $p_1, p_2$ and costs per unit effort $c_1, c_2$, the net revenue is $(p_1q_1x - c_1)E_1 + (p_2q_2y - c_2)E_2$; at a bionomic equilibrium with both fisheries operating, $x_\infty = c_1/(p_1q_1)$ and $y_\infty = c_2/(p_2q_2)$, and a fishery closes when its cost exceeds its revenue at the biological equilibrium.
3. *(Optimal harvesting.)* For the discounted revenue $\int_0^\infty e^{-\delta t}\,[(p_1q_1x - c_1)E_1 + (p_2q_2y - c_2)E_2]\,dt$, singular (interior) optimal efforts satisfy constant shadow prices $e^{\delta t}\lambda_1 = p_1 - c_1/(q_1x)$, $e^{\delta t}\lambda_2 = p_2 - c_2/(q_2y)$: the user cost per unit effort equals the discounted future marginal profit of effort at the optimal steady state.

## Depends on

- [Positive solutions lie on level curves](../../../lotka-volterra-predator-prey-model/first-integral-eq.md)

## Expansion

Boundedness follows by combining the prey logistic bound with $e x + y$, whose derivative is bounded by a constant minus a multiple of itself. The source's Theorem 5.1 also claims that an interior equilibrium $E^*=(x^*,y^*)$ is globally asymptotically stable when $4rme(1+ak)(1+ax^*)>pm^2y^{*2}$; that claim is false and is not stated here: $r=2.9356$, $k=104.7043$, $p=1.6904$, $m=0.0213$, $a=0.2082$, $e=0.572$, $d=0.0691$, $q_1=0.635$, $E_1=1.2644$, $q_2=0.1071$, $E_2=1.2547$ give three interior equilibria with $my<1$, each satisfying the inequality, which are an unstable focus, a saddle and a node. Because the refuge term $1 - my$ weakens predation exactly when predators are abundant, increasing $m$ damps the predator–prey oscillation; numerically, the refuge coefficient can remove the limit cycle and stabilize the coexistence state. The optimal-harvesting conditions are Pontryagin's maximum principle with controls entering linearly (singular arcs).

## Sources

- Md. Manarul Haque, Sahabuddin Sarwardi, "Dynamics of a Harvested Prey–Predator Model with Prey Refuge Dependent on Both Species", International Journal of Bifurcation and Chaos 28 (2018), 1830040, <https://doi.org/10.1142/s0218127418300409>. Published version of arXiv:1703.09275, cited next; locators there refer to the arXiv version.
- Md. Manarul Haque, Sahabuddin Sarwardi, "Dynamics of a harvested prey-predator model with prey refuge depended on both species", arXiv (2017). Proposition 1, Theorem 1, Section 6 (bionomic equilibrium), Section 7 (optimal harvesting policy). <https://doi.org/10.48550/arXiv.1703.09275>
