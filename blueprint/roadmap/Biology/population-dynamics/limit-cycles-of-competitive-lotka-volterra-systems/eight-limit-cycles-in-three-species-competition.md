# Eight limit cycles in three-species competition

**Model.** Three competing species with abundances $x_1,x_2,x_3>0$, measured in units of their positive equilibrium, follow

$$\dot x_i=-x_i\sum_{j=1}^3A_{ij}(x_j-1),\qquad i=1,2,3,$$

with an interaction matrix $A=(A_{ij})$ whose entries are all strictly positive, so every species' per capita growth rate decreases as any species becomes more abundant and $(1,1,1)$ is an interior equilibrium. The intrinsic growth rates are the row sums of $A$.

**Theorem.** For each $m=5,6,7,8$ there is an explicit rational positive matrix $A_m$ for which the system has at least $m$ distinct hyperbolic limit cycles in the positive octant. Ordered by decreasing radius on a fixed half-plane section through the equilibrium, the certified cycles alternate between attracting and saddle type, starting with an attracting cycle. In particular three-dimensional competitive Lotka-Volterra systems can have at least eight limit cycles, which proves the existence part of the Gyllenberg-Yan conjecture (at least five).

## Expansion

Competitive Lotka-Volterra systems in $\mathbb{R}^3_+$ have a two-dimensional carrying simplex (Hirsch), so the dynamics is essentially planar and isolated periodic orbits are possible, unlike in two dimensions. The construction tunes $A$ so that $(1,1,1)$ is a weak focus of order $m$ on the Hopf hypersurface, with parameter directions that vary the first $m-1$ focus (Lyapunov) quantities independently. Choosing these so that the drift of a scalar amplitude function alternates in sign on $m$ nested level curves forces a cycle between consecutive curves; a perturbation transverse to the Hopf hypersurface adds one more small cycle inside. For the order-eight critical matrix the first nonzero term of the one-turn displacement has degree seventeen, so at most eight small cycles bifurcate there and the count is sharp locally. Rigorous interval integration of the original equations certifies that each predicted orbit closes and determines its transverse multipliers. Ecologically, a single set of competition coefficients can support several coexisting oscillatory regimes with alternating stability.

## Sources

- Haoyu Albert Wang, Yuxiu Shao, Wei P. Dai, "Eight limit cycles in a three-dimensional competitive Lotka-Volterra system", arXiv:2611.29524 (2026), Theorem 1 (Section 1), <https://doi.org/10.48550/arXiv.2611.29524>
