# Value of a timed Kogge–Stone round

Let $M$ be a monoid (not necessarily commutative). A *timed computation* returns a value together with a cost pair $(w, r) \in \mathbb{N} \times \mathbb{N}$; a tick adds a given pair, sequencing adds the costs componentwise, and returning a value costs $(0, 0)$. Here $w$ counts monoid multiplications (work) and $r$ counts scheduled parallel rounds; list traversal, indexing, allocation, copying and recursive calls cost nothing.

For every $k \in \mathbb{N}$ and every list $y$ in $M$, the value returned by the timed round $k$ on $y$ equals the untimed round $k$ on $y$: the list of length $|y|$ whose entry $i$ is $y_{i - 2^k} \, y_i$ when $2^k \le i$ and $y_i$ when $i < 2^k$.

## Sources

- P. M. Kogge and H. S. Stone, *A parallel algorithm for the efficient solution of a general class of recurrence equations*, IEEE Transactions on Computers, 1973.
- W. D. Hillis and G. L. Steele, *Data parallel algorithms*, Communications of the ACM, 1986.
