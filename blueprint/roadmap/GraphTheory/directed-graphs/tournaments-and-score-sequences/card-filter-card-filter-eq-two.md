# Players beating both others in a three-player set of a tournament

Let $T$ be a tournament on the players $0, 1, \dots, n-1$: $T(i, j)$ means that $i$ beats $j$, no player beats itself, and for any two distinct players $i, j$ exactly one of $T(i, j)$ and $T(j, i)$ holds. Let $S$ be a set of exactly three players, and call $S$ a circular triad of $T$ when every player of $S$ beats exactly one player of $S$. The number of players $i \in S$ that beat both other players of $S$, that is, with $|\{ j \in S : T(i, j) \}| = 2$, is $0$ if $S$ is a circular triad of $T$ and $1$ otherwise.

## Sources

- J. W. Moon, *Topics on Tournaments*, Holt, Rinehart and Winston, 1968.
- Ian R. Harris and Ryan P. A. McShane, "Counting Tournaments with a Specified Number of Circular Triads", *Journal of Integer Sequences* 27 (2024), Article 24.8.7, <https://cs.uwaterloo.ca/journals/JIS/VOL27/McShane/mcshane1.html>.
