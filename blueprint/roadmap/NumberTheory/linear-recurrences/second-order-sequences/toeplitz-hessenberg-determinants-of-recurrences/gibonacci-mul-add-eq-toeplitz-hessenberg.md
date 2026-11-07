# Multiples of a shifted Gibonacci sequence that are Toeplitz–Hessenberg determinants

Let
$y$ and $z$ be non-negative integers, not both zero, and let $(G_k)$ be the Gibonacci sequence
with $G_0 = y$ and $G_1 = z$. For complex numbers $a, b, c, d$ and $n \ge 1$, let
$u_n(a, b, c, d)$ be the determinant of the $n \times n$ matrix whose entry in row $i$ and column
$j$ is $a$ if $j = i + 1$, is $(bp + c) d^p$ with $p = i - j + 1$ if $j \le i$, and is $0$ if
$j > i + 1$. Let $m \ge 3$ and let $k$ be a nonzero complex number. There are complex numbers
$a, b, c, d$ with $k G_{n+m} = u_n(a, b, c, d)$ for every $n \ge 1$ if and only if there is a
complex number $D$ with $D^2 = (-1)^m (y^2 + yz - z^2)$ and
$k = (G_{m+2} + G_m + 2D) / G_{m+1}^2$.

This is the uniqueness part of Theorem 2 of the source. The case $k = 0$ is excluded: there any
$a, b, c$ with $d = 0$ work trivially, since $u_n(a, b, c, 0) = 0$.

## Sources

- Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Theorem 2 (`integers-2025-A97-thm-2`).
