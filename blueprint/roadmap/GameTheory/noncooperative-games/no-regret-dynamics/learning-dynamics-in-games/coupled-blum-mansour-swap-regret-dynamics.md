# Coupled Blum–Mansour swap-regret dynamics

Fix a finite game and a horizon $T$. In *Blum–Mansour dynamics* each player $i$ with $m_i = |S_i|$ strategies runs $m_i$ copies of Hedge, one per strategy $a$, each with learning rate $\sqrt{m_i \ln m_i / T}$. In each round the copies' distributions $q^t_{i,a}$ form a stochastic matrix $Q^t_i$, player $i$ plays a stationary distribution $p^t_i = p^t_i Q^t_i$, and copy $a$ is charged the cost vector scaled by $p^t_i(a)$. All players run simultaneously, coupled through the product profile $p^t$.

## Depends on

- [Hedge (multiplicative-weights) dynamics in a finite game](hedge-multiplicative-weights-dynamics-in-a-finite-game.md)
- [Swap regret](../../../not-yet-classified/part-02/regret/swap-regret.md)

## Sources

- Avrim Blum and Yishay Mansour, "From External to Internal Regret", Journal of Machine Learning Research, 2007.
