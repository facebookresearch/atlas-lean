# Cost of the timed Kogge–Stone scan

Let $M$ be a monoid (not necessarily commutative). A *timed computation* returns a value together with a cost pair $(w, r) \in \mathbb{N} \times \mathbb{N}$; a tick adds a given pair, sequencing adds the costs componentwise, and returning a value costs $(0, 0)$. Here $w$ counts monoid multiplications (work) and $r$ counts scheduled parallel rounds; list traversal, indexing, allocation, copying and recursive calls cost nothing.

For every $K \in \mathbb{N}$ and every list $y$ in $M$ of length $n$, the timed scan with $K$ rounds on $y$ has cost exactly

$$\Bigl(\sum_{k=0}^{K-1} \bigl(n \mathbin{\dot-} 2^k\bigr),\ K\Bigr),$$

where $\dot-$ is truncated subtraction: its work is the total work of $K$ Kogge–Stone rounds on $n$ positions, and it schedules exactly $K$ rounds, idle rounds included. The round count is the number of requested rounds, not the longest path of a task graph.

## Sources

- P. M. Kogge and H. S. Stone, *A parallel algorithm for the efficient solution of a general class of recurrence equations*, IEEE Transactions on Computers, 1973.
- W. D. Hillis and G. L. Steele, *Data parallel algorithms*, Communications of the ACM, 1986.
