# Gallager's matrices are regular

For every choice of the column permutations, [Gallager's matrix](gallager-matrix.md) with
$n = mk$ is $(j, k)$-regular: each column has exactly one $1$ in each of the $j$ blocks, and each row
has exactly $k$ ones. So it is an $(n, j, k)$ parity-check matrix, as Gallager's construction
intends.

## Informally uses

- [Indices with a given quotient](card-filter-div-eq.md): row $(t, r)$ has ones on $\pi_t^{-1}$ of
  the $k$ columns with quotient $r$.

## Background

- [Regular low-density parity-check matrix](is-regular.md)

## Sources

- R. G. Gallager, *Low-Density Parity-Check Codes*, MIT Press, 1963, Section 2.2 (p. 13 of the author's retypeset PDF, web.mit.edu/gallager/www/pages/ldpc.pdf).
