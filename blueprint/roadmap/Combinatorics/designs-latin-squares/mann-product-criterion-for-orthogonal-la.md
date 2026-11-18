# Mann's product criterion for orthogonal Latin squares

Let $n$ be a natural number,
write $[n] = \{0, \dots, n-1\}$, and let $A$ and $B$ be Latin squares of order $n$ with rows,
columns and entries indexed by $[n]$: every row and every column of each square is a bijection
of $[n]$. For a row index $i$ write $A_i$ and $B_i$ for the permutations $j \mapsto A_{ij}$ and
$j \mapsto B_{ij}$ of $[n]$. Then the map $(i, j) \mapsto (A_{ij}, B_{ij})$ is a bijection of
$[n] \times [n]$ (that is, $A$ and $B$ are orthogonal) if and only if the square $C$ with
entries $C_{ij} = A_i(B_i^{-1}(j))$ is a Latin square, meaning that every row $j \mapsto C_{ij}$
and every column $i \mapsto C_{ij}$ of $C$ is a bijection of $[n]$.

The equivalence holds as soon as every row of $A$ and of $B$ is a permutation of $[n]$. Every row of $C$ is then automatically a permutation of $[n]$, so the content of the right side is that every column of $C$ is a permutation of $[n]$.
