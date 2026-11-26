# Unbiased high-dimensional predictions give downstream decision makers no swap regret

Consider sequential prediction of an adversarially chosen state $s_t \in [0,1]^d$ by a forecast $\hat s_t$, required to be unbiased conditional on every event $E$ in a family $\mathcal{E}$ of conditioning events (functions of the context, the history and the forecast): $\big\|\sum_{t \le T} \mathbf{1}[E(\hat s_t, x_t)]\,(\hat s_t - s_t)\big\|_\infty$ small for every $E \in \mathcal{E}$. There are efficient algorithms achieving this with bias growing sublinearly in $T$ and logarithmically in $|\mathcal{E}|$. Choosing $\mathcal{E}$ to consist of the best-response regions of polynomially many downstream decision makers with linear utilities in $s_t$, each decision maker who best responds to the forecasts attains optimal (sublinear) swap regret, simultaneously; the construction extends to large combinatorial action spaces, to extensive-form games, and to online multiclass prediction sets with multigroup coverage.

## Proof sketch

Unbiasedness conditioned on the event "decision maker $i$ best-responds with action $a$" says that, on the rounds where $i$ plays $a$, the average realized state equals the average forecast, so any swap $a \mapsto a'$ gains at most the conditional bias times the utility's Lipschitz constant. The unbiased predictions themselves are obtained by a minimax argument: at each round, a forecast that is unbiased against the adversary's mixed strategy exists, and an exponential-weights potential over the events tracks the cumulative biases.

## Depends on

- [Oracle-efficient online multicalibration and omniprediction](online-multicalibration-omniprediction.md)
- [Swap regret](../../../GameTheory/not-yet-classified/part-02/regret/swap-regret.md)
- [No-swap-regret dynamics converge to correlated equilibria](../../../GameTheory/noncooperative-games/no-regret-dynamics/no-swap-regret-dynamics-converge-to-correlated-equilibria.md)

## Proof depends on

- [Oracle-efficient online multicalibration and omniprediction](online-multicalibration-omniprediction.md)
- [Swap regret](../../../GameTheory/not-yet-classified/part-02/regret/swap-regret.md)
- [No-swap-regret dynamics converge to correlated equilibria](../../../GameTheory/noncooperative-games/no-regret-dynamics/no-swap-regret-dynamics-converge-to-correlated-equilibria.md)

## Sources

- G. Noarov, R. Ramalingam, A. Roth, S. Xie, "High-Dimensional Prediction for Sequential Decision Making", arXiv:2310.17651 (2023).
