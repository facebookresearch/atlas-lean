# Sparse table range-minimum query

For a sparse table $t$ over a type with a minimum operation
and natural numbers $l, r$, the query over $[l, r)$ returns none when $r \le l$. Otherwise, with
$k = \lfloor \log_2 (r - l) \rfloor$, it returns the option minimum (the minimum, with none as a
neutral element on either side) of the entries of $t$ at level $k$ and indices $l$ and $r - 2^k$,
in this order, where an entry not stored in $t$ counts as none.
