# Value of the timed interleaving step

Let $M$ be a monoid (not necessarily commutative). A *timed computation* returns a value together with a cost pair $(w, r) \in \mathbb{N} \times \mathbb{N}$; a tick adds a given pair, sequencing adds the costs componentwise, and returning a value costs $(0, 0)$. Here $w$ counts monoid multiplications (work) and $r$ counts scheduled parallel rounds; list traversal, indexing, allocation, copying and recursive calls cost nothing.

For all lists $zs$ and $xs$ in $M$, the value returned by the timed expansion of $zs$ along $xs$ equals the untimed expansion $(z_0, z_0 x_0, z_1, z_1 x_2, \dots)$, which stops at the first $i$ for which $z_i$ or $x_{2i+1}$ does not exist.

## Sources

- G. E. Blelloch, *Prefix sums and their applications*, Technical Report CMU-CS-90-190, Carnegie Mellon University, 1990.
- J. JáJá, *An Introduction to Parallel Algorithms*, Chapter 2.
