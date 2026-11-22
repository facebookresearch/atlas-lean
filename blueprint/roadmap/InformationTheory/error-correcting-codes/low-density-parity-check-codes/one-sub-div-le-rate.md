# Rate of a regular low-density parity-check code

Let $H$ be a $(j, k)$-regular parity-check matrix with $n > 0$ columns, $k > 0$. Its
[code](../linear-codes/of-parity-check.md) $C$ has rate

$$\frac{\dim C}{n} \ge 1 - \frac{j}{k}.$$

This is Gallager's remark that an $(n, j, k)$ parity-check matrix "has $nj/k$ rows and thus a rate
$R \ge 1 - j/k$". The rate can be larger, because the rows need not be linearly independent; in
Gallager's ensemble at least $j - 1$ of them are dependent.

## Informally uses

- [Number of rows of a regular parity-check matrix](card-rows-mul-eq.md)
- [Dimension of a code given by parity checks](card-sub-card-le-finrank.md)

## Sources

- R. G. Gallager, *Low-Density Parity-Check Codes*, MIT Press, 1963, Section 2.2 (p. 13 of the author's retypeset PDF, web.mit.edu/gallager/www/pages/ldpc.pdf).
