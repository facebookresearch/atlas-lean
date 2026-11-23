# Scheduled rounds of the timed Blelloch scan

Let $M$ be a monoid (not necessarily commutative). A *timed computation* returns a value together with a cost pair $(w, r) \in \mathbb{N} \times \mathbb{N}$; a tick adds a given pair, sequencing adds the costs componentwise, and returning a value costs $(0, 0)$. Here $w$ counts monoid multiplications (work) and $r$ counts scheduled parallel rounds; list traversal, indexing, allocation, copying and recursive calls cost nothing.

For every $k \in \mathbb{N}$ and every list $xs$ in $M$ of length exactly $n = 2^k$, the timed Blelloch scan with parameter $k$ on $xs$ schedules exactly $2k = 2\log_2 n$ rounds (the second component of its cost), idle rounds included.

## Sources

- G. E. Blelloch, *Prefix sums and their applications*, Technical Report CMU-CS-90-190, Carnegie Mellon University, 1990.
- J. JáJá, *An Introduction to Parallel Algorithms*, Chapter 2.
