# Classification of similar-strategy invasions near singular strategies in fluctuating environments

**Setting.** As in the invasion-implies-substitution article: strategies $x_i = x + \epsilon\xi_i$ in a stochastic, ergodic resident–environment system with invasion fitness $S_x(y)$, and frequency $P^\epsilon$ of $x_2$. Suppose $x$ is singular along the deviation, $\partial_y S_x(y)|_{y=x}(\xi_2 - \xi_1) = 0$, and let

$$C_{11} = \tfrac12\partial_{xx}S_x(y)|_{y=x},\quad C_{21} = \tfrac12\partial_{yx}S_x(y)|_{y=x},\quad C_{22} = \tfrac12\partial_{yy}S_x(y)|_{y=x}.$$

On the slower time $t_2 = \epsilon^2 t$ the averaged frequency obeys

$$\dot{\bar P} = \bar P(1 - \bar P)\Big((\xi_2 + \xi_1)^\top(C_{22} + C_{21})(\xi_2 - \xi_1) + \big(\tfrac12 - \bar P\big)(\xi_2 - \xi_1)^\top(C_{22} + C_{11})(\xi_2 - \xi_1)\Big),$$

whose equilibria in $[0,1]$ are $0$, $1$ and $S_{x_1}(x_2)/\big(S_{x_1}(x_2) + S_{x_2}(x_1)\big)$.

**Theorem (classification).** Under the square-integrability hypothesis, if $(\xi_2 - \xi_1)^\top(C_{22} + C_{11})(\xi_2 - \xi_1) \ne 0$ then, in the sense that $P^\epsilon$ stays $\delta$-close to the attractor of the averaged system for all large $t_2$ with probability one as $\epsilon \to 0$:
1. $S_{x_1}(x_2) > 0 > S_{x_2}(x_1)$: $x_2$ substitutes $x_1$;
2. $S_{x_1}(x_2) < 0 < S_{x_2}(x_1)$: $x_1$ persists alone;
3. $S_{x_1}(x_2) > 0$ and $S_{x_2}(x_1) > 0$: protected coexistence at $p^* = S_{x_1}(x_2)/(S_{x_1}(x_2) + S_{x_2}(x_1))$;
4. both negative: bistability, with the two exclusion outcomes having probabilities summing to one.

If instead $(\xi_2 - \xi_1)^\top(C_{22} + C_{11})(\xi_2 - \xi_1) = 0$ but $(\xi_2 + \xi_1)^\top(C_{22} + C_{21})(\xi_2 - \xi_1) \ne 0$, only boundary equilibria exist and invasion again implies substitution (cases 1–2).

## Depends on

- [Invasion implies substitution for similar strategies in stochastic environments](invasion-implies-substitution-for-similar-strategies-in-stochastic-environments.md)
- [Mutual invasibility](../../../../classification-of-adaptive-dynamics-singular-str/mutual-invasibility.md)

## Expansion

The second-order expansion of the two invasion fitnesses gives $S_{x_1}(x_2)(1 - \bar P) - S_{x_2}(x_1)\bar P = \epsilon^2$ times the bracket above, so the averaged equation is the replicator equation of a two-strategy game whose payoff gaps are the mutual invasion fitnesses, and its phase portrait is fixed by their signs, as in Lotka–Volterra competition. For scalar strategies the condition $C_{22} + C_{11} \ne 0$ is the non-degeneracy of a generic singular strategy, and $C_{22} + C_{11} > 0$ is the mutual-invasibility (coexistence) condition familiar from deterministic adaptive dynamics; environmental stochasticity enters only through the invariant measure $\mu$ used to compute $S$.

## Sources

- Y. Cai, S. A. H. Geritz, "Resident-invader dynamics of similar strategies in fluctuating environments", Journal of Mathematical Biology 81 (2020) 907–959, Sect. 2, equations (2.12)–(2.16), Lemma 2, Theorem 2, Theorem 3 and Appendix D, <https://doi.org/10.1007/s00285-020-01532-8>, PMCID: PMC7560957.
