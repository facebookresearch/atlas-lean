# Generating function of colored Arndt compositions with $k$ parts

For every $k \ge 0$,
let $C_k(x) = \sum_{n \ge 0} c(n, k)\, x^n$ in $\mathbb{Z}[[x]]$, where $c(n, k)$ is the number of
colored Arndt compositions of $n$ with $k$ parts. Then
$C_k(x)\, (1 - x)^{2k} (1 + x)^{3\lfloor k/2 \rfloor} =
x^{k + \lfloor k/2 \rfloor} (x^2 + x + 2)^{\lfloor k/2 \rfloor}$.

Equivalently, since $(1 - x)^{2k} (1 + x)^{3\lfloor k/2 \rfloor}$ has constant term $1$,
$C_k(x) = \frac{x^{k + \lfloor k/2 \rfloor} (x^2 + x + 2)^{\lfloor k/2 \rfloor}}
{(1 - x)^{2k} (1 + x)^{3\lfloor k/2 \rfloor}}$.

## Sources

- Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer Sequences 28 (2025), Article 25.3.6, Theorem 19 (`jis-2025-25.3.6-thm-19`).
