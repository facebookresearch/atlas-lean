# Infinite-time predator blow-up under abundant additional food

**Model.** A pest population $x(t)$ with logistic growth (carrying capacity $\gamma$) is consumed by an introduced predator $y(t)$ with a Holling type II response, while the predator is also supplied with additional food of quantity $\xi>0$ and quality parameter $\alpha$ (handling-time ratio). In nondimensional form

$$\frac{dx}{dt}=x\Big(1-\frac x\gamma\Big)-\frac{xy}{1+\alpha\xi+x},\qquad \frac{dy}{dt}=\frac{\beta xy}{1+\alpha\xi+x}+\frac{\beta\xi y}{1+\alpha\xi+x}-\delta y,$$

with conversion efficiency $\beta>0$ and predator death rate $\delta>0$.

**Theorem.** Assume the additional food is of high quality, $\beta-\delta\alpha>0$, and abundant, $\xi>\dfrac{\delta}{\beta-\delta\alpha}$. Then every solution with positive initial condition satisfies

$$(x(t),y(t))\to(0,\infty)\qquad(t\to\infty),$$

so the pest is driven to extinction only asymptotically (never in finite time) while the predator population grows without bound.

## Expansion

At $x=0$ the predator equation reduces to $\dot y=y\big(\beta\xi/(1+\alpha\xi)-\delta\big)$, whose growth rate is positive exactly when $\xi(\beta-\delta\alpha)>\delta$. Under this condition $\dot y\ge y\,\big(\beta\xi/(1+\alpha\xi+x)-\delta\big)$ stays bounded below by a positive rate once $x$ is small, so $y$ grows exponentially; in turn the predation term $xy/(1+\alpha\xi+x)$ forces $x\to0$, and $x$ never reaches zero in finite time because $\dot x\ge -x\,y/(1+\alpha\xi)$. Hence the classical claim that sufficiently much high-quality additional food eradicates the pest relies on an unbounded predator population, which is not a pragmatic biocontrol strategy and motivates density-dependent predator mortality induced by the additional food.

## Sources

- Rana D. Parshad, Sureni Wickramsooriya, Kwadwo Antwi-Fordjour and Aniket Banerjee, "Additional Food Causes Predators to Explode — Unless the Predators Compete", International Journal of Bifurcation and Chaos 33 (2023), 2350034, <https://doi.org/10.1142/s0218127423500347>; numbering as in arXiv:2208.00153: Section 2.3 (model with type II response) and Section 2.4 (Theorem 2.2).
