# Amortized cost of dynamic-table insertion

For a dynamic table $T$ with item count $n$
and capacity (number of slots) $m$, let $\Phi(T) = 2n - m$, an integer that may be negative.
If inserting an item $x$ into $T$ has cost $c$ and returns the table $T'$, then
$c + \Phi(T') - \Phi(T) \le 3$. Here the cost of an insertion is one unit for writing $x$ plus
one unit for each old slot copied when a full table is doubled.
