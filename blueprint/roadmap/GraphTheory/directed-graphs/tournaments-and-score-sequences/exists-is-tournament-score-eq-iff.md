# Landau's theorem for unsorted score sequences

Let $n$ be a natural number and $s : \{0, 1, \dots, n-1\} \to \mathbb{N}$. There is a tournament on the players $0, 1, \dots, n-1$ in which every player $i$ beats exactly $s(i)$ players if and only if

$$\sum_{i \in S} s(i) \ge \binom{|S|}{2} \quad \text{for every } S \subseteq \{0, 1, \dots, n-1\} \qquad \text{and} \qquad \sum_{i=0}^{n-1} s(i) = \binom{n}{2}.$$

Here a tournament is a relation $T$, with $T(i, j)$ meaning that $i$ beats $j$, such that no player beats itself and for any two distinct players $i, j$ exactly one of $T(i, j)$ and $T(j, i)$ holds. The sequence $s$ need not be sorted.

## Sources

- H. G. Landau, "On dominance relations and the structure of animal societies. III. The condition for a score structure", *Bulletin of Mathematical Biophysics* 15 (1953), 143–148.
- Ian R. Harris and Ryan P. A. McShane, "Counting Tournaments with a Specified Number of Circular Triads", *Journal of Integer Sequences* 27 (2024), Article 24.8.7, <https://cs.uwaterloo.ca/journals/JIS/VOL27/McShane/mcshane1.html>.
