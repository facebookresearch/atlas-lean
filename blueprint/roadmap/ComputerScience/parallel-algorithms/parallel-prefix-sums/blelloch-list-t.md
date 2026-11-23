# Timed Blelloch list scan

Let $M$ be a monoid (not necessarily commutative). A *timed computation* returns a value together with a cost pair $(w, r) \in \mathbb{N} \times \mathbb{N}$; a tick adds a given pair, sequencing adds the costs componentwise, and returning a value costs $(0, 0)$. Here $w$ counts monoid multiplications (work) and $r$ counts scheduled parallel rounds; list traversal, indexing, allocation, copying and recursive calls cost nothing.

For $k \in \mathbb{N}$ and a list $xs$ in $M$, the timed Blelloch scan is defined by recursion on $k$. With $k = 0$ it returns the one-element list $(1)$ at cost $(0, 0)$, whatever $xs$ is. With $k + 1$ it ticks $(0, 1)$ for the pair round, computes the timed adjacent pair products $ps$ of $xs$, runs the timed Blelloch scan with parameter $k$ on $ps$ obtaining $zs$, ticks $(0, 1)$ for the expansion round, and returns the timed expansion of $zs$ along $xs$. Each level schedules both rounds even when they perform no multiplication.

## Sources

- G. E. Blelloch, *Prefix sums and their applications*, Technical Report CMU-CS-90-190, Carnegie Mellon University, 1990.
- J. JáJá, *An Introduction to Parallel Algorithms*, Chapter 2.
