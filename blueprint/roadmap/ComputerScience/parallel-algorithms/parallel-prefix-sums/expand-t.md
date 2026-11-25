# Timed interleaving step of Blelloch's list scan

Let $M$ be a monoid (not necessarily commutative). A *timed computation* returns a value together with a cost pair $(w, r) \in \mathbb{N} \times \mathbb{N}$; a tick adds a given pair, sequencing adds the costs componentwise, and returning a value costs $(0, 0)$. Here $w$ counts monoid multiplications (work) and $r$ counts scheduled parallel rounds; list traversal, indexing, allocation, copying and recursive calls cost nothing.

For lists $z = (z_0, z_1, \dots)$ and $x = (x_0, x_1, \dots)$ in $M$, the timed expansion walks $z$ one entry at a time and $x$ two entries at a time: while both $z_i$ and the pair $(x_{2i}, x_{2i+1})$ exist, it ticks $(1, 0)$ and emits $z_i$ followed by $z_i x_{2i}$; it stops at the first $i$ for which $z_i$ or $x_{2i+1}$ does not exist. Its value is $(z_0, z_0 x_0, z_1, z_1 x_2, \dots)$. The caller charges the scheduled round.

## Sources

- G. E. Blelloch, *Prefix sums and their applications*, Technical Report CMU-CS-90-190, Carnegie Mellon University, 1990.
- J. JáJá, *An Introduction to Parallel Algorithms*, Chapter 2.
