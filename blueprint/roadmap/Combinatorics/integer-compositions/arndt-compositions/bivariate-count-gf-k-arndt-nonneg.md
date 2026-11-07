# Generating function of $k$-Arndt compositions for $k \ge 0$

Let $k \ge 0$ be an
integer, let $a_k(n, m)$ be the number of $k$-Arndt compositions of $n$ with $m$ parts, and let
$A_k(x, y) = \sum_{n \ge 0} \sum_{m=0}^{n} a_k(n, m)\, x^n y^m \in \mathbb{Z}[y][[x]]$. Then
$A_k(x, y)\,(1 - x - x^2 + x^3 - x^{3+k}y^2) = (1 - x^2)(1 - x(1 - y))$, that is,
$A_k(x, y) = (1 - x^2)(1 - x(1 - y))/(1 - x - x^2 + x^3 - x^{3+k}y^2)$.

## Sources

- Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions Approach*, INTEGERS 24 (2024), Article A35, Theorem 11, case `k ≥ 0` (`integers-2024-A35-thm-11`).
