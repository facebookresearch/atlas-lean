# Unconditional regret matching has vanishing expected regret

Let $A$ be a nonempty finite set of actions, $B$ a set of opponent actions and $c : A \times B \to \mathbb{R}$
a cost, and let $R$ bound the norms of the regret vectors. If the decision maker plays at each round the
mixed action $q_t$ of unconditional regret matching, computed from the average expected regret
vector of the previous rounds, then against every sequence $(b_t)$ of opponent actions and for
every action $k$

$$\frac1n \sum_{t < n} \Bigl(\sum_a q_t(a)\, c(a, b_t) - c(k, b_t)\Bigr) \le \frac{2R}{\sqrt n} \qquad (n \ge 1).$$

This is the expected-payoff form of Hart and Mas-Colell's Theorem B (Hart 2005, Proposition 4):
unconditional regret matching is Hannan-consistent. The almost-sure statement for realised
payoffs needs, in addition, a strong law of large numbers.

## Informally uses

- [Regret matching meets Blackwell's condition with equality](inner-pos-part-mixed-payoff-urm.md):
  the half-space condition at each round.
- [The M/√t rate of approachability](../blackwell-approachability/inf-dist-average-le.md): the
  approachability recursion applied to the nonpositive orthant.
- [Distance to the nonpositive orthant](norm-pos-part-eq-inf-dist.md): the nearest points.

## Background

- [No-regret dynamics converge to coarse correlated equilibria](is-coarse-correlated-eq-empirical.md):
  what vanishing regret for every player gives.
- [Hedge algorithm](../../../ComputerScience/machine-learning/online-learning-and-boosting/hedge-algorithm/README.md):
  another Hannan-consistent algorithm.

## Sources

- S. Hart and A. Mas-Colell, "A simple adaptive procedure leading to correlated equilibrium", Econometrica 68(5) (2000), 1127–1150, §3, Theorem B.
- S. Hart, "Adaptive heuristics", Econometrica 73(5) (2005), 1401–1430, §10.1, Proposition 4.
