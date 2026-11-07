# Generating function for weak ascent sequences avoiding 101, 102, 110 and 201

Let $a_n$
be the number of weak ascent sequences of length $n$ that avoid each of the patterns $101$,
$102$, $110$ and $201$, and let $F = \sum_{n \ge 0} a_n X^n$ in $\mathbb{Q}[[X]]$. For every
power series $S \in \mathbb{Q}[[X]]$ with $S^2 = 1 - 4X$ and constant term $1$,

$$F \cdot 2(1 - X)(1 - 4X - X^2) = (2 - 3X - X^2) S - X - X^2.$$

Such an $S$ is the power series $\sqrt{1 - 4X}$, and $1 - X$ and $1 - 4X - X^2$ are invertible,
so this is the formula
$F = \frac{(2 - 3X - X^2)\sqrt{1 - 4X} - X - X^2}{2(1 - X)(1 - 4X - X^2)}$ with the denominator
cleared.

## Sources

- David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80, Theorem 12 (`integers-2025-A80-thm-12`).
