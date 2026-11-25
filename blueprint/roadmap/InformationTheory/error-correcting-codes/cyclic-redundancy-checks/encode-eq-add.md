# CRC encoding in characteristic 2

Let $F$ be a field of characteristic 2 (for example
$\mathbb{F}_2$), let $g$ and $m$ be polynomials over $F$, and let $r$ be the degree of $g$ (with
$r = 0$ when $g = 0$). Then the CRC encoding of $m$ with generator $g$ equals
$m X^r + (m X^r \bmod g)$: the encoder appends the remainder to the shifted message.
