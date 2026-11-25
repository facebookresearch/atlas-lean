# Cost of the timed Blelloch scan

Let $M$ be a monoid (not necessarily commutative). A *timed computation* returns a value together with a cost pair $(w, r) \in \mathbb{N} \times \mathbb{N}$; a tick adds a given pair, sequencing adds the costs componentwise, and returning a value costs $(0, 0)$. Here $w$ counts monoid multiplications (work) and $r$ counts scheduled parallel rounds; list traversal, indexing, allocation, copying and recursive calls cost nothing.

Let $W$ and $S$ be the work and round recurrences of Blelloch's scan: $W(0) = 0$, $W(k+1) = 2^k + W(k) + 2^k$, and $S(0) = 0$, $S(k+1) = S(k) + 2$. For every $k \in \mathbb{N}$ and every list $xs$ in $M$ of length exactly $2^k$, the timed Blelloch scan with parameter $k$ on $xs$ has cost exactly $\bigl(W(k), S(k)\bigr)$.

## Sources

- G. E. Blelloch, *Prefix sums and their applications*, Technical Report CMU-CS-90-190, Carnegie Mellon University, 1990.
- J. JáJá, *An Introduction to Parallel Algorithms*, Chapter 2.
