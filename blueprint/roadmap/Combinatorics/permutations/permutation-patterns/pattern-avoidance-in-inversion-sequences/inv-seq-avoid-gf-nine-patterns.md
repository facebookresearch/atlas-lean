# Inversion sequences avoiding nine patterns

Let
$B = \{000, 010, 100, 101, 102, 110, 120, 201, 210\}$, where a pattern is written as a digit
string ($101$ is the triple $(1, 0, 1)$), and let
$F_B(x) = \sum_{n \ge 1} |I_n(B)| x^n \in \mathbb{Q}[[x]]$ be the generating function of the
inversion sequences avoiding every pattern in $B$. For every power series $s \in \mathbb{Q}[[x]]$
with constant term $1$ and $s^2 = 1 - 2x - 3x^2$,

$$2x^2(1 + x) F_B(x) = 2 - 3x - 3x^2 + (x - 2) s.$$

This is the closed form
$F_B(x) = (2 - 3x - 3x^2 + (x - 2)\sqrt{1 - 2x - 3x^2}) / (2x^2(1 + x))$ with the denominator
cleared, $s$ standing for $\sqrt{1 - 2x - 3x^2}$.

## Sources

- Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24 (2024), Article A76, Theorem 22 (`integers-2024-A76-thm-22`).
