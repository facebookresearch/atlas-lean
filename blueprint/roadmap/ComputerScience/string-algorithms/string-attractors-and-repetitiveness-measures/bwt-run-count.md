# Number $r$ of runs in the Burrows–Wheeler transform

For a string $T$ with an appended unique smallest sentinel, let $\mathrm{BWT}(T)$ be its Burrows–Wheeler transform. The measure $r(T)$ is the number of maximal runs of equal letters in $\mathrm{BWT}(T)$. A row $j$ of the BWT matrix is a *run start* if $j = 1$ or $\mathrm{BWT}[j] \ne \mathrm{BWT}[j-1]$.

## Depends on

- [Burrows–Wheeler transform](../burrows-wheeler-transform-and-fm-index/bwt.md)

## Sources

- Michael Burrows, David J. Wheeler, "A Block-Sorting Lossless Data Compression Algorithm", Digital SRC Research Report 124 (1994).
- Travis Gagie, Gonzalo Navarro, Nicola Prezza, "Fully Functional Suffix Trees and Optimal Text Searching in BWT-Runs Bounded Space", Journal of the ACM 67(1) (2020); SODA (2018), arXiv:1809.02792.
