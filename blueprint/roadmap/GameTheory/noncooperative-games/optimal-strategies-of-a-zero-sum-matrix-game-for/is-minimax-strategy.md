# Minimax strategy of a zero-sum matrix game

Let $A$ be an $m \times n$ real matrix, read as the zero-sum game in which the row player, playing the mixed strategy $p \in \Delta_m$ against the column player's $q \in \Delta_n$, receives $p^{\mathsf T} A q$ and the column player pays it; $\Delta_k$ is the set of probability vectors in $\mathbb{R}^k$, which is empty when $k = 0$. A column strategy $q \in \Delta_n$ is minimax when

$$\sup_{p \in \Delta_m} p^{\mathsf T} A q = \inf_{q' \in \Delta_n} \sup_{p \in \Delta_m} p^{\mathsf T} A q'.$$

Infima and suprema are those of real numbers, totalised: over an empty or unbounded set, $\inf$ and $\sup$ take the value $0$. For $m \ge 1$ the inner supremum is over a nonempty bounded set, and it is the most the row player can get against $q$; the condition says $q$ concedes at most the minimax value. For $m = 0$ the row player has no strategy, both sides are $0$, and every column strategy is minimax, with no opponent strategy attaining the bound.
