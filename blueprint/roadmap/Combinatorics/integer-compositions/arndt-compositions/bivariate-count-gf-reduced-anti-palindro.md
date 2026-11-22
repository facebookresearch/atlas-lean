# Generating function of reduced anti-palindromic compositions

Let $b(n, m)$ be the number
of reduced anti-palindromic compositions of $n$ with $m$ parts, and let
$B_p(x, y) = \sum_{n \ge 0} \sum_{m = 0}^{n} b(n, m)\, x^n y^m$ in $\mathbb{Z}[y][[x]]$, where
$x$ marks the weight and $y$ the number of parts. Then

$$B_p(x, y)\,(1 - x - x^2 + x^3 - x^3 y^2) = 1 - x - x^2 + x^3 + xy - x^3 y,$$

that is, $B_p(x, y) = (1 - x - x^2 + x^3 + xy - x^3 y)/(1 - x - x^2 + x^3 - x^3 y^2)$.

## Sources

- Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions Approach*, INTEGERS 24 (2024), Article A35, Corollary 3.
