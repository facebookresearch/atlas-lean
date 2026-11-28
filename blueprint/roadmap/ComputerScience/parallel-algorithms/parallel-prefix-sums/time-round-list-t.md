# Cost of a timed Kogge–Stone round

Let $M$ be a monoid (not necessarily commutative). A *timed computation* returns a value together with a cost pair $(w, r) \in \mathbb{N} \times \mathbb{N}$; a tick adds a given pair, sequencing adds the costs componentwise, and returning a value costs $(0, 0)$. Here $w$ counts monoid multiplications (work) and $r$ counts scheduled parallel rounds; list traversal, indexing, allocation, copying and recursive calls cost nothing.

For every $k \in \mathbb{N}$ and every list $y$ in $M$ of length $n$, the timed round $k$ on $y$ has cost exactly

$$\bigl(n \mathbin{\dot-} 2^k,\ 1\bigr),$$

where $\dot-$ is truncated subtraction on $\mathbb{N}$ ($n \mathbin{\dot-} 2^k = 0$ when $n \le 2^k$): one multiplication for each position $i$ with $2^k \le i < n$, and one scheduled round.

## Sources

- P. M. Kogge and H. S. Stone, *A parallel algorithm for the efficient solution of a general class of recurrence equations*, IEEE Transactions on Computers, 1973.
- W. D. Hillis and G. L. Steele, *Data parallel algorithms*, Communications of the ACM, 1986.
