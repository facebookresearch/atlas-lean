# Generating polynomial of rook placements covering all rows and columns

For all natural numbers $n$ and $m$, let $E_{n,m}(k)$ be the number of $k$-element sets of cells of the $n \times m$ board that contain a cell in every row and a cell in every column. In the integer polynomial ring $\mathbb{Z}[X]$,

$$\sum_{k=0}^{nm} E_{n,m}(k)\, X^k = (-1)^{n+m} \sum_{\ell=0}^{n} \sum_{k=0}^{m} \binom{n}{\ell} \binom{m}{k} (-1)^{k+\ell} (1 + X)^{k\ell}.$$
