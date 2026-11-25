# Sufficiency of Landau's condition on tournament scores

Let $n$ be a natural number and $s : \{0, 1, \dots, n-1\} \to \mathbb{N}$. Suppose that $\sum_{i \in S} s(i) \ge \binom{|S|}{2}$ for every set $S \subseteq \{0, 1, \dots, n-1\}$ and that $\sum_{i=0}^{n-1} s(i) = \binom{n}{2}$. Then there is a tournament $T$ on the players $0, 1, \dots, n-1$ in which every player $i$ beats exactly $s(i)$ players. Here a tournament is a relation $T$, with $T(i, j)$ meaning that $i$ beats $j$, such that no player beats itself and for any two distinct players $i, j$ exactly one of $T(i, j)$ and $T(j, i)$ holds.

## Sources

- H. G. Landau, "On dominance relations and the structure of animal societies. III. The condition for a score structure", *Bulletin of Mathematical Biophysics* 15 (1953), 143–148.
- Ian R. Harris and Ryan P. A. McShane, "Counting Tournaments with a Specified Number of Circular Triads", *Journal of Integer Sequences* 27 (2024), Article 24.8.7, <https://cs.uwaterloo.ca/journals/JIS/VOL27/McShane/mcshane1.html>.
