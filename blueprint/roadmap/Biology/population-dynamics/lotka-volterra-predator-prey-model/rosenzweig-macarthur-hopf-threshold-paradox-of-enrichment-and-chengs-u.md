# Rosenzweig–MacArthur model: the paradox of enrichment

For the normalized predator–prey model with logistic prey and a type II functional response,

$$\dot x = x\Bigl(1 - \frac{x}{K}\Bigr) - y\frac{x}{1 + x}, \qquad \dot y = \delta y\frac{x}{1 + x} - \gamma y,$$

with $K, \gamma, \delta > 0$ and $\alpha = \gamma/\delta < 1$, the prey and predator isoclines meet at the coexistence equilibrium $x_3 = \alpha/(1 - \alpha)$, $y_3 = (1 + x_3)(1 - x_3/K)$, which lies in the open quadrant when $x_3 < K$. The Jacobian there is $\begin{pmatrix} \alpha(1 - (1 + 2x_3)/K) & -\alpha \\ \delta(1 - \alpha)^2 y_3 & 0 \end{pmatrix}$, whose determinant is positive, so the equilibrium is locally asymptotically stable when the trace $\alpha(1 - (1 + 2x_3)/K)$ is negative, that is $K < 1 + 2x_3$, and unstable when $K > 1 + 2x_3$; at $K = 1 + 2x_3$ the system undergoes a Hopf bifurcation (paradox of enrichment article, section Link with Hopf bifurcation). Enriching the prey's carrying capacity beyond this value destabilizes the equilibrium: Rosenzweig's paradox of enrichment. As $K$ increases the model passes from predator extinction (prey-only equilibrium stable), through a stable coexistence equilibrium, to an unstable equilibrium surrounded by a limit cycle whose amplitude grows with $K$ (de Roos, Quantitative Biology, Chapter 11, Figures 11.1–11.2).

## Proof depends on

- [Poincaré–Bendixson theorem](../../../Dynamics/low-dimensional-dynamics/poincar-bendixson-theorem/poincare-bendixson.md)

## Expansion

1. The model, positivity and boundedness of solutions, and the equilibria.
2. The linearization at the coexistence equilibrium and the sign change of its trace at $K = 1 + 2x_3$; in unnormalized form $S' = \gamma_0 S(1 - S/K) - (m/y) xS/(a + S)$, $x' = x(mS/(a + S) - D_0)$, the threshold reads $K = a + 2\lambda$ with $\lambda = a D_0/(m - D_0)$.
3. Global attraction of the prey-only state for $K \le x_3$ and of the coexistence equilibrium for $x_3 < K < 1 + 2x_3$, by Lyapunov functions and the [Poincaré–Bendixson theorem](../../../Dynamics/low-dimensional-dynamics/poincar-bendixson-theorem/poincare-bendixson.md).
4. Existence of a limit cycle for $K > 1 + 2x_3$ by Poincaré–Bendixson, and its uniqueness and stability (Cheng 1981), as a separate statement.

## Sources

- Paradox of enrichment, Wikipedia, section Link with Hopf bifurcation. <https://en.wikipedia.org/wiki/Paradox_of_enrichment>
- A. M. de Roos, *Quantitative Biology*, lecture notes, University of Amsterdam, Chapter 11 (Hopf bifurcation in a predator–prey model).
- Original result: M. L. Rosenzweig, Paradox of enrichment: destabilization of exploitation ecosystems in ecological time, Science 171 (1971), 385–387. <https://doi.org/10.1126/science.171.3969.385> The destabilization by enrichment follows the paradox of enrichment article.
