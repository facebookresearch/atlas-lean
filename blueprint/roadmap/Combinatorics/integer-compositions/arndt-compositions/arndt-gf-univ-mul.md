# Generating function of all Arndt compositions

Let $A(x, y)$ be the formal power series
in $x$ over $\mathbb{Z}[y]$ whose coefficient of $x^n y^k$ is the number of Arndt compositions of
$n$ with $k$ parts. Then

$$A(x, y) \left((1 - x)(1 - x^2) - y^2 x^3\right) = (1 - x + xy)(1 - x^2).$$

Equivalently, $A(x, y) = (1 + xy/(1 - x)) \sum_{m \ge 0} y^{2m} x^{3m} / (x; x)_2^m$ with
$(x; x)_2 = (1 - x)(1 - x^2)$.

## Sources

- Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer Sequences 28 (2025), Article 25.3.6, Theorem 9 (`jis-2025-25.3.6-thm-9`).
