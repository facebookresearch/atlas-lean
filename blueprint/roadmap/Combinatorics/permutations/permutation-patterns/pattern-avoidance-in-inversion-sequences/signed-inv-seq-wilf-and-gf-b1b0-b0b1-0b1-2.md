# Signed inversion sequences avoiding $\{\bar1\bar0, \bar0\bar1, 0\bar1, 00\}$

For a set $B$
of length-2 signed patterns (a bar marks a barred letter), let $|\bar I_n(B)|$ be the number of
signed inversion sequences of length $n$ avoiding every pattern of $B$, and let
$F_B(x) = \sum_{n \ge 0} |\bar I_n(B)| x^n \in \mathbb{Q}[[x]]$. Let
$B = \{\bar1\bar0, \bar0\bar1, 0\bar1, 00\}$ and $C = \{\bar10, \bar0\bar1, 0\bar1, 00\}$. Then
$|\bar I_n(B)| = |\bar I_n(C)|$ for every $n \ge 0$, and for every $n \ge 0$ the coefficient of
$x^n$ in $F_B(x)$ equals the coefficient of $x^n$ in
$\sum_{j=0}^{n} x^j \prod_{i=1}^{j+1} (1 - ix)^{-1}$.

The terms with $j > n$ are divisible by $x^{n+1}$, so this says
$F_B(x) = \sum_{j \ge 0} x^j / \prod_{i=1}^{j+1} (1 - ix)$.

## Sources

- Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2 Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C60).
