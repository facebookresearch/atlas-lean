# Three-player sets in which a given player beats both others

Let $T$ be a tournament on the players $0, 1, \dots, n-1$: $T(i, j)$ means that $i$ beats $j$, no player beats itself, and for any two distinct players $i, j$ exactly one of $T(i, j)$ and $T(j, i)$ holds. The score $s_T(i)$ of player $i$ is the number of players that $i$ beats. For every player $i$, the number of three-element sets $S$ of players with $i \in S$ in which $i$ beats both other players of $S$ equals $\binom{s_T(i)}{2}$.

## Sources

- J. W. Moon, *Topics on Tournaments*, Holt, Rinehart and Winston, 1968.
- Ian R. Harris and Ryan P. A. McShane, "Counting Tournaments with a Specified Number of Circular Triads", *Journal of Integer Sequences* 27 (2024), Article 24.8.7, <https://cs.uwaterloo.ca/journals/JIS/VOL27/McShane/mcshane1.html>.
