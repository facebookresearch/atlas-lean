# Necessity of Landau's condition on tournament scores

Let $T$ be a tournament on the players $0, 1, \dots, n-1$: $T(i, j)$ means that $i$ beats $j$, no player beats itself, and for any two distinct players $i, j$ exactly one of $T(i, j)$ and $T(j, i)$ holds. The score $s_T(i)$ of player $i$ is the number of players that $i$ beats. For every set $S$ of players,

$$\binom{|S|}{2} \le \sum_{i \in S} s_T(i).$$

## Sources

- H. G. Landau, "On dominance relations and the structure of animal societies. III. The condition for a score structure", *Bulletin of Mathematical Biophysics* 15 (1953), 143–148.
- Ian R. Harris and Ryan P. A. McShane, "Counting Tournaments with a Specified Number of Circular Triads", *Journal of Integer Sequences* 27 (2024), Article 24.8.7, <https://cs.uwaterloo.ca/journals/JIS/VOL27/McShane/mcshane1.html>.
