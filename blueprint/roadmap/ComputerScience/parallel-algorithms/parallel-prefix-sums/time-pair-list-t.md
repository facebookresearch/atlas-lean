# Cost of the timed pair phase

Let $M$ be a monoid (not necessarily commutative). A *timed computation* returns a value together with a cost pair $(w, r) \in \mathbb{N} \times \mathbb{N}$; a tick adds a given pair, sequencing adds the costs componentwise, and returning a value costs $(0, 0)$. Here $w$ counts monoid multiplications (work) and $r$ counts scheduled parallel rounds; list traversal, indexing, allocation, copying and recursive calls cost nothing.

For every list $xs$ in $M$ of length $n$, the timed pair phase on $xs$ has cost exactly

$$\bigl(\lfloor n/2 \rfloor,\ 0\bigr):$$

one multiplication per complete input pair and no rounds.

## Sources

- G. E. Blelloch, *Prefix sums and their applications*, Technical Report CMU-CS-90-190, Carnegie Mellon University, 1990.
- J. JáJá, *An Introduction to Parallel Algorithms*, Chapter 2.
