# Eight-pattern sets differing in 201 and 210: equivalence and generating function

Write a
length-3 pattern as the word of its values, so $101$ is the pattern $(1, 0, 1)$. For a set $B$ of
patterns let $|I_n(B)|$ be the number of inversion sequences of length $n$ that avoid every
pattern in $B$, and let $F_B(x) = \sum_{n \ge 1} |I_n(B)| x^n \in \mathbb{Q}[[x]]$. Let
$B_\tau = \{000, 010, 100, 101, 102, 110, 120, \tau\}$. Then $|I_n(B_{201})| = |I_n(B_{210})|$
for every $n \ge 0$, and for every power series $s \in \mathbb{Q}[[x]]$ with constant term $1$
and $s^2 = 1 - 2x - 3x^2$,

$$
2x^3 (1 + x)(x^2 + 2x + 2) F_{B_{201}}(x) =
1 - x^2 - 4x^3 - 7x^4 - 5x^5 - 2x^6 - (1 + x + 2x^2 + 2x^3 + x^4) s.
$$

This is the paper's closed form for $F_{B_{201}}$ with the denominator cleared, where $s$ plays
the role of $\sqrt{1 - 2x - 3x^2}$.

## Sources

- Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24 (2024), Article A76, Theorem 17.
