# Bivariate generating function of a two-index count

For a function $a$ assigning a natural
number $a(n, m)$ to every pair of natural numbers $n, m$, its bivariate generating function is the
power series $\sum_{n \ge 0} \bigl(\sum_{m = 0}^{n} a(n, m)\, y^m\bigr) x^n$ in
$\mathbb{Z}[y][[x]]$, where $x$ marks the first index (the weight) and $y$ the second. Only the
terms with $m \le n$ enter; for counts with $a(n, m) = 0$ whenever $m > n$ it equals
$\sum_{n, m} a(n, m)\, x^n y^m$.

## Sources

- Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions Approach*, INTEGERS 24 (2024), Article A35, Section 2 (the series `A(x, y)`, `Ap(x, y)`, `Bp(x, y)`, `B(x, y)`, `A_k(x, y)` and `A^{(k)}(x, y)`).
