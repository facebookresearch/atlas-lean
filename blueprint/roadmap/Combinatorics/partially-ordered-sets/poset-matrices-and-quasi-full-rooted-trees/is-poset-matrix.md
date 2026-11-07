# Poset matrix

An $n \times n$ Boolean matrix $M$, with rows and columns indexed by
$\{0, \dots, n-1\}$, is an upper-triangular $(0, 1)$-poset matrix when its entries strictly
below the main diagonal are false ($M_{ij}$ is false whenever $j < i$), its diagonal entries
$M_{ii}$ are true, and its true entries are transitive: if $M_{ij}$ and $M_{jk}$ are true,
then $M_{ik}$ is true.

## Sources

- JIS `mohammad3.tex`, lines 171–176, SHA-256 `839f29b85b01af033998ae2ca01fb12acb8b055b72ed095859474eb3f746a2b8`.
