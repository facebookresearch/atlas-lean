# Signed inversion sequences avoiding $\{\bar1\bar0, \bar0\bar1, \bar00, 00\}$

For a set $B$
of length-2 signed patterns (a bar marks a barred letter), let $|\bar I_n(B)|$ be the number of
signed inversion sequences of length $n$ avoiding every pattern of $B$, and let
$F_B(x) = \sum_{n \ge 0} |\bar I_n(B)| x^n \in \mathbb{Q}[[x]]$. Let
$B_1 = \{\bar1\bar0, \bar0\bar1, \bar00, 00\}$, $B_2 = \{\bar1\bar0, \bar0\bar1, 0\bar0, 00\}$ and
$B_3 = \{\bar10, \bar0\bar1, 0\bar0, 00\}$. Then
$|\bar I_n(B_1)| = |\bar I_n(B_2)| = |\bar I_n(B_3)|$ for every $n \ge 0$, and for every $n \ge 0$
the coefficient of $x^n$ in $F_{B_1}(x)$ equals the coefficient of $x^n$ in

$$
\frac{1}{1 - x} + \frac{1}{1 - x} \sum_{j=1}^{n} \frac{x^j (1 - jx)}{\prod_{i=1}^{j+1} (1 - ix)}.
$$

The terms with $j > n$ are divisible by $x^{n+1}$, so this says
$F_{B_1}(x) = \frac{1}{1 - x}\Bigl(1 + \sum_{j \ge 1} x^j (1 - jx) /
\prod_{i=1}^{j+1} (1 - ix)\Bigr)$.

## Sources

- Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2 Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C46) (`integers-2026-A74-thm-3`).
