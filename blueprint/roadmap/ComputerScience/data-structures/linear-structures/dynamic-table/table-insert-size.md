# Capacity after an insertion

Let $T$ be a dynamic table with item count $n$ and capacity
(number of slots) $m$, and let $x$ be an item. The table returned by inserting $x$ into $T$ with
TABLE-INSERT has capacity $1$ if $m = 0$, capacity $2m$ if $m > 0$ and $n = m$, and capacity $m$
otherwise.
