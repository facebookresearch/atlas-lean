# Low-density parity-check codes

Gallager's low-density parity-check codes (1962, 1963) are the binary linear codes of sparse
parity-check matrices. An $(n, j, k)$ matrix has $n$ columns, $j$ ones in each column and $k$ ones in
each row; counting its ones by rows and by columns shows that its number $r$ of rows satisfies
$rk = nj$, so for $n, k > 0$ it has $r = nj/k$ rows and its code has rate at least $1 - j/k$. For
$n = mk$, Gallager's ensemble stacks $j$ blocks of $m$ rows: the first block has its ones in
consecutive runs of $k$ columns, and each further block is the first with its columns permuted at
random. Every matrix of the ensemble is $(n, j, k)$-regular.

## Regular parity-check matrices

- [Column weight of a matrix](col-weight.md)
- [Row weight of a matrix](row-weight.md)
- [Regular low-density parity-check matrix](is-regular.md)
- [Row and column weights have the same total](sum-row-weight-eq-sum-col-weight.md)
- [Number of rows of a regular parity-check matrix](card-rows-mul-eq.md)
- [Dimension of a code given by parity checks](card-sub-card-le-finrank.md)
- [Rate of a regular low-density parity-check code](one-sub-div-le-rate.md)

## Gallager's ensemble

- [Column permutations of Gallager's ensemble](block-perm.md)
- [Gallager's $(n, j, k)$ matrix with $n = mk$](gallager-matrix.md)
- [Indices with a given quotient](card-filter-div-eq.md)
- [Gallager's matrices are regular](is-regular-gallager-matrix.md)
- [Rate of Gallager's low-density codes](one-sub-div-le-rate-gallager-matrix.md)

## Related topics

- [Linear codes](../linear-codes/README.md): codes given by a parity-check matrix, their dimension
  and syndrome decoding.
- [Bounds on code size](../bounds-on-code-size/README.md): the Gilbert bound, to which Gallager
  relates the minimum distance of random parity-check codes (his Section 2.1).
- [Random coding bound and Gallager's exponent](../../channel-coding/random-coding-bound-and-gallager-s-exponent/README.md):
  Gallager's error-exponent analysis of random codes.
