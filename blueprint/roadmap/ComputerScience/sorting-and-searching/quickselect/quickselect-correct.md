# Correctness of quickselect

Let $L$ be a list over a linear order and let $k$ be a
natural number. If quickselect on $L$ with zero-based rank $k$ returns an element $x$, then $x$
is an entry of $L$, and, counting entries of $L$ with multiplicity, the number of entries less
than $x$ is at most $k$ and $k$ is less than the number of entries at most $x$.

Thus $x$ occupies zero-based position $k$ in the sorted order of $L$, also when $x$ is repeated.
