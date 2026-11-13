# Formula for the generating function of even-length down/up compositions

Let
$F(x, y, z) \in \mathbb{Q}[[x, y, z]]$ be the generating function of down/up compositions with an
even number of parts (including the empty composition, with last part $0$) by weight ($x$),
number of parts ($y$) and last part ($z$). For a power series $w$, write
$(xw; x)_m = \prod_{i=1}^{m} (1 - x^i w)$ and let

$$\alpha(x, y, w) = \sum_{n \ge 0} \frac{(-1)^n x^{n^2+n} y^{2n} w^n}{(xw; x)_{2n}}$$

and

$$\beta(x, y, w) = \sum_{n \ge 1} \frac{(-1)^{n+1} x^{n^2+n} y^{2n} w^n}{(1 - x)(xw; x)_{2n-1}},$$

with the sums taken coefficientwise. Then

$$F(x, y, z) = \alpha(x, y, z) + \frac{\alpha(x, y, x)\, \beta(x, y, z)}{1 - \beta(x, y, x)}.$$

## Sources

- Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer Sequences 28 (2025), Article 25.3.6, Theorem 12 (`jis-2025-25.3.6-thm-12`).
