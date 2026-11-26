# Competitive exclusion of prey strategies under a shared predator

**Model.** Prey strategies are pairs $(c, r)$ in a feasible set $Q \subset \mathbb R^2$ (attack rate suffered, reproduction rate); prey densities $z(v,t)$ and one predator $F(t)$ satisfy

$$\partial_t z(v,t) = r(v)z(v,t) - c(v)z(v,t)F(t) - z(v,t)\int_V z(u,t)\,\mu^*(du), \qquad \dot F = F\int_V c(v)z(v,t)\,\mu^*(dv) - F,$$

with predator mortality and conversion efficiency equal to one. The long-run per-capita growth of strategy $(c,r)$ is $r - c\langle F\rangle$ minus the time-averaged total prey density, which is common to all strategies, so the ranking is by $r - c\langle F\rangle$.

**Single survivor.** If only $(c_0, r_0)$ survives, the equilibrium gives $\langle F\rangle = r_0/c_0 - 1/c_0^2$, and the associated fitness

$$Y_1(c, r; c_0, r_0) = r - c\Big(\frac{r_0}{c_0} - \frac{1}{c_0^2}\Big)$$

satisfies $Y_1(c_0, r_0; c_0, r_0) = 1/c_0$. The strategy $(c_0, r_0)$ is best among those initially present iff $Y_1(c, r; c_0, r_0) < 1/c_0$ for all of them, so the ranking depends on which strategies are present initially.

**Exclusion.** Two strategies $(c_1,r_1)$, $(c_2,r_2)$ can be the only survivors only if, with $\langle F\rangle = (r_2 - r_1)/(c_2 - c_1)$, every other present strategy has $r - c\langle F\rangle$ smaller than at $(c_1, r_1)$ and $(c_2, r_2)$, i.e. lies strictly below the line through them in the $(c, r)$ plane; if $Q$ is strictly convex this fails, so generically a single strategy, the maximizer $(c^*, r^*)$ of $Y_1(\cdot;c^*,r^*)$ over $Q$, survives. For strictly convex $Q$, an everywhere-dense random sequence of candidate strategies eventually places, with probability one, a point in every $\epsilon$-neighbourhood of $(c^*, r^*)$, which justifies Monte Carlo localization of the optimum.

## Depends on

- [Ranking order of strategies and fitness reconstruction under clonal inheritance](ranking-order-and-fitness-reconstruction-under-clonal-inheritance.md)

## Expansion

At a one-strategy equilibrium the predator equation forces $c_0 z = 1$ and the prey equation then gives $F = (r_0 - 1/c_0)/c_0$. Because fitness is linear in $(c, r)$ for fixed $\langle F\rangle$, its level sets are straight lines, and the best strategy is the point of $Q$ supporting the highest such line; strict convexity makes that support point unique and puts other points of $Q$ above any chord, ruling out two-strategy coexistence. Three or more survivors require equal fitness, which is structurally unstable.

## Sources

- S. K. Sandhu, A. Morozov, O. Kuzenkov, "Revealing evolutionarily optimal strategies in self-reproducing systems via a new computational approach", Bulletin of Mathematical Biology 81 (2019) 4701–4725, Sect. 2.3: equations (8)–(11) and Proposition 1, <https://doi.org/10.1007/s11538-019-00663-4>, PMCID: PMC6874526.
