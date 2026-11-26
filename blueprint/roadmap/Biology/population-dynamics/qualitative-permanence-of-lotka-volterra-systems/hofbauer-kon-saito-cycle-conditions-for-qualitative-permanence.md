# Hofbauer-Kon-Saito cycle conditions for qualitative permanence

Consider the Lotka-Volterra system on $X = \mathbb R^n_{\ge 0}$,
$$\dot x_i = x_i\Big(r_i + \sum_{j=1}^n a_{ij}x_j\Big), \qquad i = 1, \dots, n.$$
It is *permanent* if there is $\delta > 0$ with $\delta \le \liminf_{t\to\infty} x_i(t) \le \limsup_{t\to\infty} x_i(t) \le 1/\delta$ for all $i$ and every solution starting in the interior. Let $Q_A$ be the set of matrices with the same sign pattern as $A$. The matrix $A$ is *qualitatively permanent* if the system is permanent for every $\tilde A \in Q_A$ and every $r \in \mathbb R^n$ for which an interior equilibrium exists (equivalently, $\dot x_i = x_i\sum_j \tilde a_{ij}(x_j - x_j^*)$ is permanent for every $\tilde A \in Q_A$ and $x^* > 0$); no sign condition is placed on $r$. A *cycle* of $A$ is a product $a_{i_1i_2}a_{i_2i_3}\cdots a_{i_ki_1}$ over distinct indices with $k \ge 2$.

**Theorem (Hofbauer, Kon and Saito, 2008).** Let $a_{ii} < 0$ for all $i$. If $A$ is qualitatively permanent, then

- (C1) every cycle of $A$ of length at least $2$ is $\le 0$, and
- (C2) every negative cycle of $A$ contains exactly one negative entry.

For $n \le 3$, (C1) and (C2) are also sufficient.

Hofbauer, Kon and Saito conjectured that (C1) and (C2) characterize qualitative permanence for every $n$; they proved it for generalized food-chain patterns.

## Expansion

Condition (C1) excludes positive feedback loops, which for some admissible magnitudes produce multiple interior equilibria or loss of stability; (C2) says every negative loop is a single consumer-resource or predator-prey link closed by mutualistic or commensal links, so no loop contains two exploitative interactions. For small communities these sign conditions force a Volterra-Lyapunov structure on the interaction matrix, from which permanence follows for every admissible magnitude.

## Sources

- M.-M. Beldiman and A.-D. Halanay, "A five-species counterexample to the Hofbauer-Kon-Saito conjecture on qualitative permanence", arXiv preprint (2026), Section 1 and Theorem 1.1, quoting J. Hofbauer, R. Kon and Y. Saito, Qualitative permanence of Lotka-Volterra equations, J. Math. Biol. (2008), Theorems 2.3 and 2.7 and Conjecture 2.4. <https://doi.org/10.48550/arXiv.2610.38374>