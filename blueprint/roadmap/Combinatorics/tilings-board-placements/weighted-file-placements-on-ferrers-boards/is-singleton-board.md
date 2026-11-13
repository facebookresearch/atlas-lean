# Singleton boards

For natural numbers $h$ and $m$, write $\lfloor h \rfloor_m$ for the
largest multiple of $m$ that is at most $h$. A list $b = (b_1, \ldots, b_n)$ of natural numbers
is a singleton board for $m$ when it is weakly increasing (the column heights of a Ferrers board)
and, for every $1 \le i < n$, $b_i - \lfloor b_i \rfloor_m \ne 0$ implies
$\lfloor b_i \rfloor_m < \lfloor b_{i+1} \rfloor_m$.

## Sources

- Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024), Article A58, Section 2.2 (definition of singleton boards).
