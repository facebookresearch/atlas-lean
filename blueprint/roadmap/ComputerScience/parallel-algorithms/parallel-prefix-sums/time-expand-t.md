# Cost of the timed interleaving step

Let $M$ be a monoid (not necessarily commutative). A *timed computation* returns a value together with a cost pair $(w, r) \in \mathbb{N} \times \mathbb{N}$; a tick adds a given pair, sequencing adds the costs componentwise, and returning a value costs $(0, 0)$. Here $w$ counts monoid multiplications (work) and $r$ counts scheduled parallel rounds; list traversal, indexing, allocation, copying and recursive calls cost nothing.

For all lists $zs$ and $xs$ in $M$, the timed expansion of $zs$ along $xs$ has cost exactly

$$\bigl(\min(|zs|,\ \lfloor |xs|/2 \rfloor),\ 0\bigr):$$

one multiplication for each scanned entry that has a complete input pair, and no rounds.

## Sources

- G. E. Blelloch, *Prefix sums and their applications*, Technical Report CMU-CS-90-190, Carnegie Mellon University, 1990.
- J. JáJá, *An Introduction to Parallel Algorithms*, Chapter 2.
