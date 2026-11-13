# Generating function for the total number of colored Arndt compositions

For $n \ge 0$ let
$c(n, k)$ be the number of colored Arndt compositions of $n$ with $k$ parts, and let
$c(n) = \sum_{k=0}^{n} c(n, k)$ be the total number of colored Arndt compositions of $n$ (so
$c(0) = 1$, counting the empty composition). Then, in the ring $\mathbb{Z}[[x]]$ of formal power
series,

$$\Big(\sum_{n \ge 0} c(n) x^n\Big) (1 - x - 3x^2 + x^3 + 2x^4 - 4x^5 - x^6 + x^7) =
(1 - x)^2 (1 + x)^3 (1 - x + x^2).$$

## Sources

- Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer Sequences 28 (2025), Article 25.3.6, Corollary 18 (`jis-2025-25.3.6-cor-18`).
