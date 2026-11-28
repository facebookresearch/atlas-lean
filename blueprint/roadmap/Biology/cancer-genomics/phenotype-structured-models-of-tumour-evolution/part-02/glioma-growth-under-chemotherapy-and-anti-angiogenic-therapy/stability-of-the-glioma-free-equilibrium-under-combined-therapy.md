# Stability of the glioma-free equilibrium under combined chemotherapy and anti-angiogenic therapy

**Model.** The nondimensional model tracks glial cells $g_1$, chemotherapy-sensitive glioma cells $g_2$, resistant glioma cells $g_3$, endothelial cells $g_4$, neurons $g_5$, the chemotherapy agent $q$ and the anti-angiogenic agent $y$. Let $F$ be the Heaviside function and $d_i(g_4, y) = d_{i0} + d_{i1}g_4 + d_{i2}y$:

$$g_1' = p_1g_1(1-g_1) - \beta_1g_1(g_2+g_3) - d_1(g_4,y)\frac{g_1q}{a_1+g_1},$$

$$g_2' = p_2g_2\Big(1 - \frac{g_2+g_3}{1+\tau g_4}\Big) - \beta_2g_1g_2 - uF(q)g_2 - \rho F(y)g_2 - d_2(g_4,y)\frac{g_2q}{a_2+g_2},$$

$$g_3' = p_3g_3\Big(1 - \frac{g_2+g_3}{1+\tau g_4}\Big) - \beta_3g_1g_3 + uF(q)g_2 - \rho F(y)g_3,$$

$$g_4' = \mu(g_2+g_3) + p_4g_4(1-g_4) - d_4\frac{g_4y}{a_4+g_4},\qquad g_5' = \alpha\,g_1'F(-g_1')\,g_5 - d_5(g_4,y)\frac{g_5q}{a_5+g_5},$$

$$q' = \phi - \Big(\psi + c_1\frac{g_1}{a_1+g_1} + c_2\frac{g_2}{a_2+g_2} + c_5\frac{g_5}{a_5+g_5}\Big)q,\qquad y' = \delta - \Big(\gamma + c_4\frac{g_4}{a_4+g_4}\Big)y .$$

Chemotherapy kills sensitive cells and converts them to resistant cells at rate $u$. Resistant cells are not killed by chemotherapy. Anti-angiogenic therapy removes both glioma types at rate $\rho$ and inhibits the endothelial support of the glioma carrying capacity $1+\tau g_4$. Neurons die when glial cells decline.

**Equilibrium.** With no cells present, the agents settle at $q_0 = \phi/\psi$ and $y_0 = \delta/\gamma$, giving the equilibrium $E_0 = (0,0,0,0,0,q_0,y_0)$.

**Theorem.** $E_0$ is locally asymptotically stable when

$$p_1 < \frac{d_1(0,y_0)\,q_0}{a_1},\qquad p_2 - u - \rho < \frac{d_2(0,y_0)\,q_0}{a_2},\qquad p_3 < \rho,\qquad p_4 < \frac{d_4\,y_0}{a_4},$$

with $d_i(0,y_0) = d_{i0} + d_{i2}\delta/\gamma$. The third condition says that resistant glioma cells are eliminated only by the anti-angiogenic agent. The fourth says that the endothelial population collapses under the anti-angiogenic agent alone, which in the paper's form reads $\delta > p_4\gamma a_4/d_4$.

## Expansion

At $E_0$ the Jacobian is triangular when the variables are ordered $g_1, g_2, g_3, g_4, g_5, q, y$. The only linear couplings are $g_2\to g_3$ (conversion $u$), $g_2, g_3\to g_4$ (angiogenic signal $\mu$) and cells $\to q$ (drug uptake); all other interactions are quadratic. The eigenvalues of the cell variables are therefore their per-capita growth rates at zero density:

- $p_1 - d_1(0,y_0)q_0/a_1$ for $g_1$;
- $p_2 - u - \rho - d_2(0,y_0)q_0/a_2$ for $g_2$;
- $p_3 - \rho$ for $g_3$;
- $p_4 - d_4y_0/a_4$ for $g_4$;
- $-d_5(0,y_0)q_0/a_5 < 0$ for $g_5$.

The agent equations contribute $-\psi$ and $-\gamma$. The Heaviside factors equal $1$ near $E_0$ because $q_0, y_0 > 0$. Requiring every eigenvalue to be negative gives the four conditions, which are equivalent to lower bounds on the infusion rates $\phi$ and $\delta$. A second, glial-dominated equilibrium $E_1 = (g_1^b, 0, 0, g_4^b, 0, q^b, y^b)$, in which glioma is cleared but healthy tissue survives, has more involved local stability conditions (Teorema 3.2).

## Proof depends on

- [Lyapunov's indirect method (linearized stability), conditional decay form](../../../../../Analysis/ordinary-differential-equations/lyapunov-s-indirect-method/global-solution-decay-of-has-fderiv-at.md)

## Sources

- L. Hanum, N. Susyanto and D. Ertiningsih, "Mathematical Model of the Impact of Chemotherapy and Anti-Angiogenic Therapy on Drug Resistance in Glioma Growth", arXiv:2308.11212 (2023), Section 2 (model) and Section 3 (Teorema 3.1 and 3.2), <https://doi.org/10.48550/arXiv.2308.11212>.
