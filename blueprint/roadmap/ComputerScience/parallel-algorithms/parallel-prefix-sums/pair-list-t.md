# Timed adjacent pair products of a list

Let $M$ be a monoid (not necessarily commutative). A *timed computation* returns a value together with a cost pair $(w, r) \in \mathbb{N} \times \mathbb{N}$; a tick adds a given pair, sequencing adds the costs componentwise, and returning a value costs $(0, 0)$. Here $w$ counts monoid multiplications (work) and $r$ counts scheduled parallel rounds; list traversal, indexing, allocation, copying and recursive calls cost nothing.

For a list $(a_0, a_1, \dots, a_{n-1})$ in $M$, the timed pair phase walks the list two entries at a time: for each complete pair $(a_{2i}, a_{2i+1})$ it ticks $(1, 0)$ and emits $a_{2i} a_{2i+1}$; when one or no entry remains it stops, discarding an unmatched last entry. Its value is $(a_0 a_1, a_2 a_3, \dots)$, of length $\lfloor n/2 \rfloor$.

## Sources

- G. E. Blelloch, *Prefix sums and their applications*, Technical Report CMU-CS-90-190, Carnegie Mellon University, 1990.
- J. JáJá, *An Introduction to Parallel Algorithms*, Chapter 2.
