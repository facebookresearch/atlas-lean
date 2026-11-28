# Adaptive heuristics

Adaptive heuristics are simple, myopic rules of behaviour for repeated games that move play in seemingly better directions (Hart 2005). The leading example is regret matching (Hart and Mas-Colell 2000): a player switches from its last action to another with probability proportional to its regret for not having made that switch in the past. When every player uses it, the empirical distribution of play converges almost surely to the set of correlated equilibria. Such dynamics are uncoupled, since each player uses only its own payoffs, and uncoupled dynamics cannot guarantee convergence to Nash equilibrium (Hart and Mas-Colell 2003). Calibrated forecasting (Foster and Vohra 1998) is a related route to correlated equilibria, built on the same regret-invariance condition.

- [Last-Iterate Convergence in Monotone Games](last-iterate-convergence-in-monotone-games/README.md)
- [Optimistic Learning Dynamics and Polylogarithmic Regret in Games](optimistic-learning-dynamics-in-games/README.md)

## Regret matching

- [Regret matching](regret-matching.md)
- [Regret matching leads to correlated equilibria](regret-matching-tendsto-correlated-eq.md)

## Uncoupled dynamics

- [Nash equilibrium of Jordan's games](jordan-eq.md)
- [Uncoupled dynamics do not lead to Nash equilibrium](not-exists-uncoupled-stable-dynamic.md)

## Calibrated forecasting

- [Calibration score](calibration-score.md)
- [Asymptotic calibration](exists-calibrated-forecast.md)

## Related topics

- [Correlated equilibria](../correlated-equilibria/README.md): the limit of regret matching, characterised by vanishing conditional regrets.
- [Blackwell approachability](../blackwell-approachability/README.md): the theory behind regret-based strategies.
- [No-regret dynamics](../no-regret-dynamics/README.md): unconditional regrets, Hannan consistency and coarse correlated equilibria.
- [Hedge algorithm](../../../ComputerScience/machine-learning/online-learning-and-boosting/hedge-algorithm/README.md): a Hannan-consistent (no external regret) algorithm, an alternative to unconditional regret matching.
- [Nash's theorem](../nash-s-theorem/README.md): the equilibria that uncoupled dynamics cannot guarantee to reach.
