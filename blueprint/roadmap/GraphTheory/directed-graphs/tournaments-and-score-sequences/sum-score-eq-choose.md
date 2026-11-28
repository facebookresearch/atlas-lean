# Sum of the scores of a tournament

Let $T$ be a tournament on the players $0, 1, \dots, n-1$: $T(i, j)$ means that $i$ beats $j$, no player beats itself, and for any two distinct players $i, j$ exactly one of $T(i, j)$ and $T(j, i)$ holds. The score $s_T(i)$ of player $i$ is the number of players that $i$ beats. Then

$$\sum_{i=0}^{n-1} s_T(i) = \binom{n}{2}.$$
