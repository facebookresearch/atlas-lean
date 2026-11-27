# Signed inversion sequences avoiding $\{\bar1\bar0, \bar0\bar1, 01\}$

For a set $B$ of
length-2 signed patterns (a bar marks a barred letter), let $|\bar I_n(B)|$ be the number of signed
inversion sequences of length $n$ avoiding every pattern of $B$, and let
$F_B(x) = \sum_{n \ge 0} |\bar I_n(B)| x^n \in \mathbb{Q}[[x]]$. Let
$B = \{\bar1\bar0, \bar0\bar1, 01\}$ and $C = \{\bar10, \bar0\bar1, 01\}$. Then
$|\bar I_n(B)| = |\bar I_n(C)|$ for every $n \ge 0$, and

$$
(1 - 2x)(1 - 3x + x^2)(1 - x)^2 F_B(x) = (1 - 2x)(1 - 3x + x^2)(1 - x)^2 + x(1 - x)^4 +
x(1 - x + x^2)(1 - 3x + x^2),
$$

that is,
$F_B(x) = 1 + \frac{x(1 - x)^2}{(1 - 2x)(1 - 3x + x^2)} + \frac{x(1 - x + x^2)}{(1 - 2x)(1 - x)^2}$.

## Sources

- Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2 Signed Patterns*, INTEGERS 26 (2026), Article A74, Lemma 5.
