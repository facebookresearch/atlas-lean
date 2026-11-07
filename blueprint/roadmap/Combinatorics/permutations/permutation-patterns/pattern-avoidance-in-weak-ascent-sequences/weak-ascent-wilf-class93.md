# Weak ascent Wilf equivalence and generating function, class 93

Write $\mathrm{WA}_n(P)$
for the set of weak ascent sequences of length $n$ avoiding every pattern in $P$, with patterns
written as words (for example $011$). The pattern sets $P = \{011, 102, 120, 201\}$ and
$\{011, 102, 120, 210\}$ are WA-Wilf equivalent, that is,
$|\mathrm{WA}_n(P)| = |\mathrm{WA}_n(\{011, 102, 120, 210\})|$ for every $n \ge 0$. Moreover, the
formal power series $F(x) = \sum_{n \ge 1} |\mathrm{WA}_n(P)| \, x^n$ in $\mathbb{Z}[[x]]$
(without the $n = 0$ term) satisfies $F(x) \, (1 - 2x)(1 - x)^2 = x(2x^2 - 2x + 1)$, that is,
$F(x) = \frac{x(2x^2 - 2x + 1)}{(1 - 2x)(1 - x)^2}$.

## Sources

- David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80, Theorem 7 (`integers-2025-A80-thm-7`).
