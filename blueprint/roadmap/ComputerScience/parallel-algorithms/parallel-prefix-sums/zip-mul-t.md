# Timed lockstep multiplication of two lists

Let $M$ be a monoid (not necessarily commutative). A *timed computation* returns a value together with a cost pair $(w, r) \in \mathbb{N} \times \mathbb{N}$; a tick adds a given pair, sequencing adds the costs componentwise, and returning a value costs $(0, 0)$. Here $w$ counts monoid multiplications (work) and $r$ counts scheduled parallel rounds; list traversal, indexing, allocation, copying and recursive calls cost nothing.

For lists $(a_0, \dots, a_{p-1})$ and $(b_0, \dots, b_{q-1})$ in $M$, the timed lockstep product walks both lists together: for each matched pair $(a_i, b_i)$, $i < \min(p, q)$, it ticks $(1, 0)$ and emits $a_i b_i$, and it stops as soon as either list is exhausted. Its value is the list $(a_0 b_0, \dots, a_{m-1} b_{m-1})$ with $m = \min(p, q)$.

## Sources

- P. M. Kogge and H. S. Stone, *A parallel algorithm for the efficient solution of a general class of recurrence equations*, IEEE Transactions on Computers, 1973.
- W. D. Hillis and G. L. Steele, *Data parallel algorithms*, Communications of the ACM, 1986.
