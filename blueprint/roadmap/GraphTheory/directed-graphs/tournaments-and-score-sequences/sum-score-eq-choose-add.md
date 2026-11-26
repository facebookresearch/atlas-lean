# Total score of a set of tournament players

Let $T$ be a tournament on the players $0, 1, \dots, n-1$: $T(i, j)$ means that $i$ beats $j$, no player beats itself, and for any two distinct players $i, j$ exactly one of $T(i, j)$ and $T(j, i)$ holds. The score $s_T(i)$ of player $i$ is the number of players that $i$ beats. For every set $S$ of players,

$$\sum_{i \in S} s_T(i) = \binom{|S|}{2} + \sum_{i \in S} \bigl|\{ j \notin S : T(i, j) \}\bigr|,$$

the games the players of $S$ win among themselves plus those they win against players outside $S$.
