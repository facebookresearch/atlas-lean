# Table-driven LF-mapping inversion of the Burrows-Wheeler transform

Let $L$ be the last column of the Burrows-Wheeler matrix of a word $w$ and $I$ the row index of $w$. Define $C[c]$ as the number of symbols of $L$ smaller than $c$ and the rank array $P[r]$ as the number of occurrences of $L[r]$ in $L[0..r-1]$. Then the LF-mapping is $T(r) = C[L[r]] + P[r]$, and $w$ is recovered backwards by $w[n-1-i] = L[T^{i}(I)]$ for $i = 0, \dots, n-1$.

## Depends on

- [Burrows–Wheeler transform](../burrows-wheeler-transform-and-fm-index/bwt.md)
- [LF-mapping from the last column](../burrows-wheeler-transform-and-fm-index/lf.md)

## Proof depends on

- [Inversion of the Burrows–Wheeler transform](../burrows-wheeler-transform-and-fm-index/invert.md)

## Sources

- M. Burrows and D. J. Wheeler, "A Block-sorting Lossless Data Compression Algorithm", technical report 124, Digital Systems Research Center, 1994.
