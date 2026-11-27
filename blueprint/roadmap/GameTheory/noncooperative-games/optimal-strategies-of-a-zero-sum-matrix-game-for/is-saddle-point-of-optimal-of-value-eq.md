# Optimal strategies form a saddle point

Let $A$ be an $m \times n$ real matrix, read as the zero-sum game in which the row player, playing the mixed strategy $p \in \Delta_m$ against the column player's $q \in \Delta_n$, receives $p^{\mathsf T} A q$ and the column player pays it; $\Delta_k$ is the set of probability vectors in $\mathbb{R}^k$, which is empty when $k = 0$. Suppose the game has a value,

$$\sup_{p \in \Delta_m} \inf_{q \in \Delta_n} p^{\mathsf T} A q = \inf_{q \in \Delta_n} \sup_{p \in \Delta_m} p^{\mathsf T} A q,$$

with infima and suprema as in the definition of a [maximin strategy](is-maximin-strategy.md). If $p$ is a maximin strategy and $q$ a [minimax strategy](is-minimax-strategy.md), then $(p, q)$ is a saddle point: $p'^{\mathsf T} A q \le p^{\mathsf T} A q$ for every $p' \in \Delta_m$, and $p^{\mathsf T} A q \le p^{\mathsf T} A q'$ for every $q' \in \Delta_n$. Both action sets are nonempty here, since $p$ and $q$ exist.
