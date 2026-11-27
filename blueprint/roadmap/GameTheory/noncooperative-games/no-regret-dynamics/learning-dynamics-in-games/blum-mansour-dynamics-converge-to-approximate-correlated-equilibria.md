# Blum–Mansour dynamics converge to approximate correlated equilibria

Let $G$ be a finite cost game with all costs in $[0, 1]$, played for $T$ rounds with mixed strategies $p^t_i$. If every player's swap regret over the coupled play is at most $R$, then the time-averaged product distribution $\psi = \frac1T \sum_t \prod_i p^t_i$ is an $(R/T)$-approximate correlated equilibrium: for every player $i$ and every map $F : S_i \to S_i$,

$$
\mathbb{E}_{s \sim \psi}\bigl[c_i(s) - c_i(F(s_i), s_{-i})\bigr] \le \frac{R}{T}.
$$

In Blum–Mansour dynamics the swap regret of player $i$ is at most $\sum_{a \in S_i} R_{i,a}$, where $R_{i,a}$ is the external regret of the copy for strategy $a$ against its scaled cost vectors $p^t_i(a)\, c^t_i$. Hence the time average is an $(R/T)$-approximate correlated equilibrium with $R = \max_i \sum_{a \in S_i} R_{i,a}$.

## Proof sketch

The stationary-distribution step makes the player's realized cost equal to the sum of the copies' charged costs, so swap regret is at most the sum of the copies' external regrets. Swap regret at most $R$ for every player is exactly the displayed condition for the time average, since the expected cost under $\psi$ is the average of the expected costs of the rounds. With the dynamics' learning rate $\sqrt{m_i \ln m_i / T}$ ($m_i = |S_i|$), the Hedge regret bound summed over the copies gives $\sum_a R_{i,a} \le 2\sqrt{T m_i \ln m_i}$ when $T \ge m_i \ln m_i$, so the slack tends to $0$ as $T$ grows.

## Depends on

- [Coupled Blum–Mansour swap-regret dynamics](coupled-blum-mansour-swap-regret-dynamics.md)
- [Correlated equilibrium](../../correlated-equilibria/is-correlated-eq.md)
- [Swap regret](../../../not-yet-classified/part-02/regret/swap-regret.md)
- [External regret](../../../not-yet-classified/part-02/regret/external-regret.md)

## Proof depends on

- [Blum–Mansour decomposition](../../../not-yet-classified/part-02/regret-blum-mansour/swap-regret-le-sum-external-regret-scale.md)
- [Each player in Hedge dynamics has vanishing regret](each-player-in-hedge-dynamics-has-vanishing-regret.md)

## Sources

- Avrim Blum and Yishay Mansour, "From External to Internal Regret", Journal of Machine Learning Research 8 (2007), 1307–1324, Theorem 3 (swap regret at most $R$ for every player makes the empirical distribution of play an $(R/T)$-correlated equilibrium) and Theorem 5 (the swap regret of the master algorithm is at most the sum of the copies' regrets).
- Avrim Blum and Yishay Mansour, "Learning, Regret Minimization, and Equilibria", Algorithmic Game Theory, Cambridge University Press, 2007, Definition 4.11, Theorem 4.12 (the empirical distribution, which gives each round's joint distribution $P^t$ weight $1/T$, is an $(R/T)$-correlated equilibrium) and Theorem 4.15 (the master procedure built from $N$ copies of an $R$-external-regret procedure has swap regret at most $NR$).
- Tim Roughgarden, "CS364A: Algorithmic Game Theory, Lecture Notes", Stanford University, Fall 2013, 2013.
