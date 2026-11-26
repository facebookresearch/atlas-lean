# Blackwell approachability

In a repeated game with vector payoffs, a closed convex set is approachable when the decision maker can force the average payoff to converge to it, whatever the opponent does. Blackwell (1956) showed that this holds exactly when every closed half-space containing the set is enforceable, that is, when each scalarised game has a minimax value on the right side of the half-space. The Blackwell strategy plays, from the current average, a mixed action that keeps the next payoff in the half-space through the nearest point of the set; the squared distance $\delta_t$ then satisfies $t^2\delta_t \le (t-1)^2\delta_{t-1} + M^2$, which gives the rate $M/\sqrt t$. Applied to the vector of regrets and the nonpositive orthant, approachability yields Hannan-consistent strategies and the strategies without conditional regret that lead to correlated equilibria (Hart and Mas-Colell 2000; Hart 2005).

- [Running average of a sequence](average.md)
- [Sum form of the running average](nat-cast-smul-average.md)
- [Recursion for the running average](succ-smul-average.md)
- [Norm bound for the running averages](norm-average-le.md)
- [One step of Blackwell's recursion](sq-succ-mul-inf-dist-average-le.md)
- [Blackwell's approachability recursion](sq-mul-inf-dist-average-le.md)
- [The M/√t rate of approachability](inf-dist-average-le.md)

## Vector-payoff games

- [Expected vector payoff of a mixed action](mixed-payoff.md)
- [Bound on expected vector payoffs](norm-mixed-payoff-le.md)
- [Blackwell's half-space step](exists-inner-sub-nonpos-of-enforceable.md)
- [Running sums of the expected payoffs of a strategy](strategy-sums.md)
- [Stage payoffs of a strategy](strategy-payoffs.md)
- [Stage payoffs add up to the running sums](sum-range-strategy-payoffs.md)
- [Blackwell's approachability theorem, expected-payoff form](blackwell-expected-approachability.md)

## Almost-sure approachability

- [σ-algebra of a history](history-sigma.md)
- [Monotonicity of the history σ-algebras](history-sigma-mono.md)
- [History σ-algebras are sub-σ-algebras](history-sigma-le.md)
- [Measurability of functions of the history](measurable-history-sigma.md)
- [Blackwell's approachability theorem](blackwell-approachability.md)

## Related topics

- [Von Neumann's minimax theorem](../von-neumann-s-minimax-theorem/README.md): Blackwell's theorem is a vector analogue; a half-space is enforceable when a scalarised game has the right minimax value.
- [Correlated equilibria](../correlated-equilibria/README.md): approaching the nonpositive orthant of conditional regrets leads to them.
- [No-regret dynamics](../no-regret-dynamics/README.md): approaching the orthant of unconditional regrets gives Hannan-consistent strategies.
- [Adaptive heuristics](../adaptive-heuristics/README.md): regret matching, a heuristic descendant of the Blackwell strategy.
