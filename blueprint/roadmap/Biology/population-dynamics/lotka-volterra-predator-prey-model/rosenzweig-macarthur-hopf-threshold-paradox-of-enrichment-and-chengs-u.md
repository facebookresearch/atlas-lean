# Rosenzweig–MacArthur model: the paradox of enrichment

For the normalized predator–prey model with logistic prey and a type II functional response,

$$\dot x = x\Bigl(1 - \frac{x}{K}\Bigr) - y\frac{x}{1 + x}, \qquad \dot y = \delta y\frac{x}{1 + x} - \gamma y,$$

with $K, \gamma, \delta > 0$ and $\alpha = \gamma/\delta < 1$, the prey and predator isoclines meet at the coexistence equilibrium $x_3 = \alpha/(1 - \alpha)$, $y_3 = (1 + x_3)(1 - x_3/K)$, which lies in the open quadrant when $x_3 < K$. The Jacobian there is $\begin{pmatrix} \alpha(1 - (1 + 2x_3)/K) & -\alpha \\ \delta(1 - \alpha)^2 y_3 & 0 \end{pmatrix}$, whose determinant is positive, so the equilibrium is locally asymptotically stable when the trace $\alpha(1 - (1 + 2x_3)/K)$ is negative, that is $K < 1 + 2x_3$, and unstable when $K > 1 + 2x_3$; this is the Rosenzweig–MacArthur criterion that the equilibrium is stable when the isoclines meet to the right of the hump of the prey isocline $y = (1 + x)(1 - x/K)$, at $x = (K - 1)/2$, and unstable when they meet to its left (Rosenzweig and MacArthur 1963; Hsu 1978, Sec. 3, where it is $x^* < K < a + 2x^*$ in unnormalized form). At $K = 1 + 2x_3$ the trace vanishes with $K$-derivative $\alpha(1 + 2x_3)/K^2 > 0$ while the determinant stays positive, so the eigenvalues cross the imaginary axis transversally: a Hopf bifurcation. Enriching the prey's carrying capacity beyond this value destabilizes the equilibrium: Rosenzweig's paradox of enrichment. For $x_3 < K < 1 + 2x_3$ the coexistence equilibrium is globally stable in the open quadrant (Hsu 1978, Theorem 3.3), and for $K > 1 + 2x_3$ the Poincaré–Bendixson theorem gives a periodic orbit around it (Hsu 1978, Sec. 4), which is the unique limit cycle and is stable (Cheng 1981).

## Proof depends on

- [Poincaré–Bendixson theorem](../../../Dynamics/low-dimensional-dynamics/poincar-bendixson-theorem/poincare-bendixson.md)

## Expansion

1. The model, positivity and boundedness of solutions, and the equilibria.
2. The linearization at the coexistence equilibrium and the sign change of its trace at $K = 1 + 2x_3$; in unnormalized form $S' = \gamma_0 S(1 - S/K) - (m/y) xS/(a + S)$, $x' = x(mS/(a + S) - D_0)$, the threshold reads $K = a + 2\lambda$ with $\lambda = a D_0/(m - D_0)$.
3. Global attraction of the prey-only state for $K \le x_3$ and of the coexistence equilibrium for $x_3 < K < 1 + 2x_3$, by Lyapunov functions and the [Poincaré–Bendixson theorem](../../../Dynamics/low-dimensional-dynamics/poincar-bendixson-theorem/poincare-bendixson.md).
4. Existence of a limit cycle for $K > 1 + 2x_3$ by Poincaré–Bendixson, and its uniqueness and stability (Cheng 1981), as a separate statement.

## Sources

- Original result: M. L. Rosenzweig, Paradox of enrichment: destabilization of exploitation ecosystems in ecological time, Science 171 (1971), 385–387. <https://doi.org/10.1126/science.171.3969.385>
- M. L. Rosenzweig and R. H. MacArthur, Graphical representation and stability conditions of predator–prey interactions, Am. Nat. 97 (1963), 209–223. <https://doi.org/10.1086/282272>
- S. B. Hsu, On global stability of a predator–prey system, Math. Biosci. 39 (1978), 1–10, Theorem 3.3 and Sec. 4. <https://doi.org/10.1016/0025-5564(78)90025-1>
- K.-S. Cheng, Uniqueness of a limit cycle for a predator–prey system, SIAM J. Math. Anal. 12 (1981), 541–548.
