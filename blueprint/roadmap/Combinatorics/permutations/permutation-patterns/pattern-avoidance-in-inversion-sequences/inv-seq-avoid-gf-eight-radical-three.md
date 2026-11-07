# A common generating function for three sets of eight patterns

Let
$B_1 = \{000, 010, 100, 101, 102, 120, 201, 210\}$,
$B_2 = \{000, 010, 100, 102, 110, 120, 201, 210\}$ and
$B_3 = \{000, 010, 101, 102, 110, 120, 201, 210\}$, where a pattern is written as a digit string
($101$ is the triple $(1, 0, 1)$). For a set $B$ of patterns let
$F_B(x) = \sum_{n \ge 1} |I_n(B)| x^n \in \mathbb{Q}[[x]]$ be the generating function of the
inversion sequences avoiding every pattern in $B$. For each $j \in \{1, 2, 3\}$ and every power
series $s \in \mathbb{Q}[[x]]$ with constant term $1$ and $s^2 = 1 - 2x - 3x^2$,

$$x^2 F_{B_j}(x) = 1 - 2x - x^2 + x^3 - (1 - x) s.$$

This is the closed form $F_{B_j}(x) = (1 - 2x - x^2 + x^3 - (1 - x)\sqrt{1 - 2x - 3x^2}) / x^2$
with the denominator cleared, $s$ standing for $\sqrt{1 - 2x - 3x^2}$.

## Sources

- Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24 (2024), Article A76, Theorem 18 (`integers-2024-A76-thm-18`).
