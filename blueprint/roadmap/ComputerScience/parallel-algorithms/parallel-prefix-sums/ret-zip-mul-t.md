# Value of timed lockstep multiplication

Let $M$ be a monoid (not necessarily commutative). A *timed computation* returns a value together with a cost pair $(w, r) \in \mathbb{N} \times \mathbb{N}$; a tick adds a given pair, sequencing adds the costs componentwise, and returning a value costs $(0, 0)$. Here $w$ counts monoid multiplications (work) and $r$ counts scheduled parallel rounds; list traversal, indexing, allocation, copying and recursive calls cost nothing.

For all lists $xs$ and $ys$ in $M$, the value returned by the timed lockstep product of $xs$ and $ys$ is the pointwise product list $\mathrm{zipWith}(\cdot)(xs, ys)$, whose entry $i$ is $xs_i \cdot ys_i$ for $i < \min(|xs|, |ys|)$.

## Sources

- P. M. Kogge and H. S. Stone, *A parallel algorithm for the efficient solution of a general class of recurrence equations*, IEEE Transactions on Computers, 1973.
- W. D. Hillis and G. L. Steele, *Data parallel algorithms*, Communications of the ACM, 1986.
