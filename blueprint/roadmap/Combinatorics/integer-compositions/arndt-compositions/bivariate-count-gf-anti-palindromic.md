# Generating function of anti-palindromic compositions

Let $ap(n, m)$ be the number of
anti-palindromic compositions of $n$ with $m$ parts, and let
$Ap(x, y) = \sum_{n \ge 0} \sum_{m=0}^{n} ap(n, m)\, x^n y^m \in \mathbb{Z}[y][[x]]$. Then
$Ap(x, y)\,(1 - x - x^2 + x^3 - 2x^3y^2) = 1 - x - x^2 + x^3 + xy - x^3y$, that is,
$Ap(x, y) = (1 - x - x^2 + x^3 + xy - x^3y)/(1 - x - x^2 + x^3 - 2x^3y^2)$.

## Sources

- Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions Approach*, INTEGERS 24 (2024), Article A35, Theorem 6 (`integers-2024-A35-thm-6`).
