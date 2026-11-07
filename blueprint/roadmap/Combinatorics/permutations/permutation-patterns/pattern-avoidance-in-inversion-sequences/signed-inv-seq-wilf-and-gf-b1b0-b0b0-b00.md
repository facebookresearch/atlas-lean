# Signed inversion sequences avoiding $\{\bar1\bar0, \bar0\bar0, \bar00, 01\}$

For a set $B$
of length-2 signed patterns (a bar marks a barred letter), let $|\bar I_n(B)|$ be the number of
signed inversion sequences of length $n$ avoiding every pattern of $B$, and let
$F_B(x) = \sum_{n \ge 0} |\bar I_n(B)| x^n \in \mathbb{Q}[[x]]$. Let
$B = \{\bar1\bar0, \bar0\bar0, \bar00, 01\}$ and $C = \{\bar1\bar0, \bar01, 0\bar1, 01\}$. Then
$|\bar I_n(B)| = |\bar I_n(C)|$ for every $n \ge 0$, and for every power series
$S \in \mathbb{Q}[[x]]$ with constant term $1$ and $S^2 = 1 - 4x$,

$$
2x(1 - x)^2(1 - 2x) F_B(x) = 1 - 3x + 2x^2 + 2x^3 - (1 - 3x + 2x^2) S.
$$

This is the formula
$F_B(x) = \bigl(1 - 3x + 2x^2 + 2x^3 - (1 - 3x + 2x^2)\sqrt{1 - 4x}\bigr)/(2x(1 - x)^2(1 - 2x))$
multiplied by its denominator, with $S = \sqrt{1 - 4x}$.

## Sources

- Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2 Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C39) (`integers-2026-A74-thm-3`).
