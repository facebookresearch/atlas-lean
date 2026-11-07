# The store returned by sentinel deletion

Let $S$ be a node store and $x$ an address
whose cell holds a node with previous address $p$ and next address $n$, where the cells at $p$
and $n$ are nonempty. Let $S_1$ be $S$ with the node at $p$ replaced by a copy whose next
address is $n$. Then sentinel deletion of $x$ from $S$ returns $S_1$ with the node of $S_1$ at
$n$ replaced by a copy whose previous address is $p$.
