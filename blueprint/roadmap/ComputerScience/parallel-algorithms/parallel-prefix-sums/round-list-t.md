# Timed round of the Kogge–Stone list scan

Let $M$ be a monoid (not necessarily commutative). A *timed computation* returns a value together with a cost pair $(w, r) \in \mathbb{N} \times \mathbb{N}$; a tick adds a given pair, sequencing adds the costs componentwise, and returning a value costs $(0, 0)$. Here $w$ counts monoid multiplications (work) and $r$ counts scheduled parallel rounds; list traversal, indexing, allocation, copying and recursive calls cost nothing.

For $k \in \mathbb{N}$ and a list $y = (y_0, \dots, y_{n-1})$ in $M$, the timed round $k$ first ticks $(0, 1)$ (one scheduled round, charged even when the round performs no multiplication), then forms the timed lockstep product of $y$ with its suffix $(y_{2^k}, \dots, y_{n-1})$, and returns the first $\min(2^k, n)$ entries of $y$ followed by those products. The result has length $n$, with entry $y_i$ at each position $i < \min(2^k, n)$ and entry $y_{i - 2^k} \, y_i$ at each position $i$ with $2^k \le i < n$.

## Sources

- P. M. Kogge and H. S. Stone, *A parallel algorithm for the efficient solution of a general class of recurrence equations*, IEEE Transactions on Computers, 1973.
- W. D. Hillis and G. L. Steele, *Data parallel algorithms*, Communications of the ACM, 1986.
