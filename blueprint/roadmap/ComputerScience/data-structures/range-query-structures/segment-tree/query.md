# Range query on a segment tree

For a segment tree $t$ with values in an additive monoid
and natural numbers $l, r$, the range query over $[l, r)$, with positions counted from the start
of the segment of $t$, is defined recursively. On the empty tree it is $0$. On a leaf with value
$x$ it is $x$ if $l = 0 < r$, and $0$ otherwise. On an internal node with cached aggregate $a$,
cached size $s$ and children $t_1, t_2$, it is $0$ if $r \le l$ or $s \le l$; otherwise it is $a$
if $l = 0$ and $s \le r$; and in all remaining cases it is the query over $[l, r)$ on $t_1$ plus
the query over $[l - m, r - m)$ on $t_2$, where $m$ is the size of $t_1$ and subtraction is
truncated at $0$.

An empty range and a node disjoint from the range contribute $0$ without descending, and a fully
covered node contributes its cached aggregate.
