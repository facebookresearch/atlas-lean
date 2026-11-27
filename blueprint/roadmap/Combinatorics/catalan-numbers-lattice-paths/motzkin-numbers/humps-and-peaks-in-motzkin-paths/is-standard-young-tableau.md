# Standard Young tableau

A standard Young tableau of order $n$ is encoded by a map $T$ that
assigns to each entry $i \in \{0, \dots, n-1\}$ a cell $T(i) = (r_i, c_i)$ with row and column
indices in $\{0, \dots, n-1\}$. The map $T$ is a standard Young tableau when it is injective
and, for every entry $i$ and every cell $(r, c)$ with $r \le r_i$ and $c \le c_i$, there is an
entry $j \le i$ with $T(j) = (r, c)$.

It follows that for every $m \le n$ the cells of the entries $0, \dots, m-1$ form a Young
diagram, and that entries increase strictly along rows and down columns.

## Sources

- Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
