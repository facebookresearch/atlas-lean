# A common generating function for three sets of seven patterns

Let
$B_1 = \{010, 011, 100, 101, 102, 201, 210\}$, $B_2 = \{010, 011, 100, 102, 110, 201, 210\}$ and
$B_3 = \{010, 011, 101, 102, 110, 201, 210\}$, where a pattern is written as a digit string ($101$
is the triple $(1, 0, 1)$). For a set $B$ of patterns let
$F_B(x) = \sum_{n \ge 1} |I_n(B)| x^n \in \mathbb{Q}[[x]]$ be the generating function of the
inversion sequences avoiding every pattern in $B$. Then for each $j \in \{1, 2, 3\}$,

$$(1 - x)(1 - 2x)^2 F_{B_j}(x) = x(1 - 2x)^2 + x^2(1 - x)^2.$$

Since $(1 - x)(1 - 2x)^2$ is a unit in $\mathbb{Q}[[x]]$, this says
$F_{B_j}(x) = x/(1 - x) + x^2(1 - x)/(1 - 2x)^2$.

## Sources

- Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24 (2024), Article A76, Theorem 16.
