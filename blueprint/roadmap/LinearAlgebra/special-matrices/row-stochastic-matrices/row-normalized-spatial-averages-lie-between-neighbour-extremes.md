# Row-normalized spatial averages lie between neighbouring extremes

Let $W$ be a nonnegative matrix whose row $i$ sums to $1$, and let $x$ be a real vector. Then $(Wx)_i = \sum_j w_{ij}x_j$ is a convex combination of the values $x_j$ with $w_{ij} > 0$, so $\min\{x_j : w_{ij} > 0\} \le (Wx)_i \le \max\{x_j : w_{ij} > 0\}$. Row normalization requires a positive row sum; rows of zeros (isolated areas) need a separate convention.

## Sources

- The statement is derived on this page from its definitions and the linked results; no external source is followed.
