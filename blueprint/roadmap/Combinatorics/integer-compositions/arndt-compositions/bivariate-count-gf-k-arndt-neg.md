# Generating function of $k$-Arndt compositions for negative $k$

Let $k' \ge 1$ and
$k = -k'$, let $a_k(n, m)$ be the number of $k$-Arndt compositions of $n$ with $m$ parts, and
let $A_k(x, y) = \sum_{n \ge 0} \sum_{m=0}^{n} a_k(n, m)\, x^n y^m \in \mathbb{Z}[y][[x]]$. Then
$A_k(x, y)\,(1 - x - x^2(1 + y^2) + x^3(1 - y^2) + y^2x^{2+k'}) = (1 - x^2)(1 - x(1 - y))$,
that is,
$A_k(x, y) = (1 - x^2)(1 - x(1 - y))/(1 - x - x^2(1 + y^2) + x^3(1 - y^2) + y^2x^{2-k})$.

## Sources

- Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions Approach*, INTEGERS 24 (2024), Article A35, Theorem 11, case `k < 0` (`integers-2024-A35-thm-11`).
