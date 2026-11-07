# Generating function of palindromic Arndt compositions

Let $PA(x, y, z)$ be the
generating function of nonempty palindromic Arndt compositions by weight ($x$), number of parts
($y$) and middle summand ($z$), and let $F(x, y, z)$ be the generating function of down/up
compositions $\sigma_1 > \sigma_2 < \sigma_3 > \cdots$ with an even number of parts by weight
($x$), number of parts ($y$) and last part ($z$). Then, as formal power series over $\mathbb{Q}$,

$$
PA(x, y, z) = \frac{xyz}{1 - xz} F(x^2, y^2, xz) +
\frac{x^3 y^3 z}{(1 - x^2)(1 - xz)} F(x^2, y^2, x^2) -
\frac{x^3 y^3 z}{(1 - xz)(1 - x^3 z)} F(x^2, y^2, x^3 z).
$$

## Sources

- Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer Sequences 28 (2025), Article 25.3.6, Theorem 14 (`jis-2025-25.3.6-thm-14`).
