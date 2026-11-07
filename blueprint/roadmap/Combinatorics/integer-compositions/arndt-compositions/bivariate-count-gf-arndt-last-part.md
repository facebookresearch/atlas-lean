# Generating function of Arndt compositions by last part

Let $b(n, m)$ be the number of
Arndt compositions of $n$ with last part $m$, where the empty composition of $0$ counts as
having last part $0$ (so $b(0, 0) = 1$), and let
$B(x, y) = \sum_{n \ge 0} \sum_{m=0}^{n} b(n, m)\, x^n y^m \in \mathbb{Z}[y][[x]]$. Then
$B(x, y)\,(1 - x - x^2)(1 - xy)(1 - x^2y) =
1 - x - x^2 - x^2y + 2x^3y + 2x^4y - x^5y - x^4y^2$.

## Sources

- Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions Approach*, INTEGERS 24 (2024), Article A35, Theorem 8 (`integers-2024-A35-thm-8`).
