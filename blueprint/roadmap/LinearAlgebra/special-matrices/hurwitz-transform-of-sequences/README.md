# Hurwitz transform of sequences

For sequences $a, b : \mathbb{N} \to R$ in a commutative ring $R$, the Hurwitz transform of $a$ and $b$ is the sequence whose $n$-th term is the determinant of the Hurwitz matrix of order $n$: the $(n + 1) \times (n + 1)$ matrix with entry $h_{ij}$ in row $i$ and column $j$, where $h_{ij} = 0$ if $i \ge 2j + 2$, $h_{ij} = a_{j - i/2}$ if $i$ is even, and $h_{ij} = b_{j - (i-1)/2}$ if $i$ is odd.

## Idea

Hurwitz matrices interleave the coefficients of two sequences in alternating rows, in the pattern of the matrix whose leading minors decide, by the Routh–Hurwitz criterion, whether a real polynomial has all its roots in the left half-plane. Barry turned the construction into a transform of sequences: the Hurwitz transform records the determinants of the successive Hurwitz matrices. The single-sequence transform pairs $a$ with the sequence $1, 0, 0, \dots$. Such transforms are studied alongside the binomial and Hankel transforms of integer sequences.

## Statements

- [Hurwitz transform](hurwitz-transform.md)
- [Hurwitz matrix](hurwitz-matrix.md): the Hurwitz matrix
- [Entries of the Hurwitz matrix](hurwitz-entry.md): its entries
- [Hurwitz transform of a single sequence](hurwitz-single.md): special case: the transform of a single sequence
