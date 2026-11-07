# Out-of-range point updates leave a Fenwick tree unchanged

Let $t$ be a Fenwick tree
over a commutative additive monoid $\alpha$, and let $n$ be its size (the length of its stored
array minus one). For every natural number $i \ge n$ and every $\delta \in \alpha$, the point
update of $t$ adding $\delta$ at position $i$ returns $t$ itself.
