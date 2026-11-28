# Games won inside a set of tournament players

Let $T$ be a tournament on the players $0, 1, \dots, n-1$: $T(i, j)$ means that $i$ beats $j$, no player beats itself, and for any two distinct players $i, j$ exactly one of $T(i, j)$ and $T(j, i)$ holds. For every set $S$ of players,

$$\sum_{i \in S} \bigl|\{ j \in S : T(i, j) \}\bigr| = \binom{|S|}{2},$$

that is, the players of $S$ win $\binom{|S|}{2}$ games against each other in total, one for each pair of distinct players of $S$.
