# Maximin strategy of a zero-sum matrix game

Let $A$ be an $m \times n$ real matrix, read as the zero-sum game in which the row player, playing the mixed strategy $p \in \Delta_m$ against the column player's $q \in \Delta_n$, receives $p^{\mathsf T} A q$ and the column player pays it; $\Delta_k$ is the set of probability vectors in $\mathbb{R}^k$, which is empty when $k = 0$. A row strategy $p \in \Delta_m$ is maximin when

$$\inf_{q \in \Delta_n} p^{\mathsf T} A q = \sup_{p' \in \Delta_m} \inf_{q \in \Delta_n} p'^{\mathsf T} A q.$$

Infima and suprema are those of real numbers, totalised: both are $0$ over the empty set, $\inf$ is $0$ over a set unbounded below, and $\sup$ is $0$ over a set unbounded above. For $n \ge 1$ the inner infimum is over a nonempty bounded set, and it is the least payoff $p$ can receive, hence the greatest lower bound $p$ guarantees against every column strategy; the condition says $p$ guarantees the maximin value. For $n = 0$ the column player has no strategy, both sides are $0$, and every row strategy is maximin, with no opponent strategy attaining the bound.
