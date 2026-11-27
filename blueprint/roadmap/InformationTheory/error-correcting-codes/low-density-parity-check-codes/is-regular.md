# Regular low-density parity-check matrix

A matrix $H$ over a field is $(j, k)$-regular if every column has exactly $j$ nonzero entries and
every row exactly $k$. For a binary matrix with $n$ columns this is Gallager's $(n, j, k)$
parity-check matrix: $j$ ones in each column, $k$ ones in each row, and zeros elsewhere. Its
[code](../linear-codes/of-parity-check.md) is an $(n, j, k)$ low-density parity-check code. The definition allows
any field; over $\mathrm{GF}(2)$ it is exactly Gallager's.

## Background

- [Column weight](col-weight.md) and [row weight](row-weight.md)
- [Code with a given parity-check matrix](../linear-codes/of-parity-check.md): the code the matrix defines.

## Sources

- R. G. Gallager, *Low-Density Parity-Check Codes*, MIT Press, 1963, Section 2.2 (p. 13 of the author's retypeset PDF, web.mit.edu/gallager/www/pages/ldpc.pdf).
