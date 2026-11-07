# Closed form of the generating function of colored Arndt compositions

Let
$C(x, y) = \sum_{n, k} c(n, k)\, x^n y^k$ in $\mathbb{Z}[y][[x]]$, where $c(n, k)$ is the number
of colored Arndt compositions of $n$ with $k$ parts. Then
$C(x, y) \cdot (1 - x - 3x^2 - x^3(2y^2 - 3) - x^4(y^2 - 3) - x^5(3 + y^2) - x^6 + x^7) =
(1 - x)^2 (1 + x)^3 (1 + x^2 + x(y - 2))$.

Since the second factor on the left has constant term $1$, this says that
$C(x, y) = \frac{(1 - x)^2 (1 + x)^3 (1 + x^2 + x(y - 2))}{1 - x - 3x^2 - x^3(2y^2 - 3) -
x^4(y^2 - 3) - x^5(3 + y^2) - x^6 + x^7}$.

## Sources

- Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer Sequences 28 (2025), Article 25.3.6, Theorem 17 (`jis-2025-25.3.6-thm-17`).
