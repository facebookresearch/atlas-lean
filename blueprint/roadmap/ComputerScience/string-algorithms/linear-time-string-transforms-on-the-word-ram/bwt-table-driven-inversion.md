# Table-driven LF-mapping inversion of the Burrows-Wheeler transform

Let $w$ be a primitive word of length $n$ (not a proper power, so its $n$ cyclic rotations are distinct), let $L$ be the last column of the Burrows-Wheeler matrix of its sorted cyclic rotations and $I$ the row index of $w$ in that matrix. Define $C[c]$ as the number of symbols of $L$ smaller than $c$ and the rank array $P[r]$ as the number of occurrences of $L[r]$ in $L[0..r-1]$. Then the LF-mapping is $T(r) = C[L[r]] + P[r]$, and $w$ is recovered backwards by $w[n-1-i] = L[T^{i}(I)]$ for $i = 0, \dots, n-1$.

## Depends on

- [Burrows–Wheeler transform](../burrows-wheeler-transform-and-fm-index/bwt.md)
- [LF-mapping from the last column](../burrows-wheeler-transform-and-fm-index/lf.md)

## Proof depends on

- [Inversion of the Burrows–Wheeler transform](../burrows-wheeler-transform-and-fm-index/invert.md)

## Sources

- M. Burrows and D. J. Wheeler, "A Block-sorting Lossless Data Compression Algorithm", technical report 124, Digital Systems Research Center, 1994.
- M. Crochemore, J. Désarménien and D. Perrin, "A note on the Burrows-Wheeler transformation", Theoretical Computer Science 332(1-3), 2005, pp. 567-572, Sections 2-3 (cyclic conjugates of a primitive word, and linear-time inversion by the standard permutation).
