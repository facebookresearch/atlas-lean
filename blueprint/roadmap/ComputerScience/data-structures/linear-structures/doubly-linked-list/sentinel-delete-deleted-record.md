# Sentinel deletion keeps the deleted node

Let $S$ be a node store and $x$ an address
whose cell holds a node with previous address $p$ and next address $n$, where the cells at $p$
and $n$ are nonempty. The cell at $x$ after sentinel deletion of $x$ from $S$ equals the cell of
$S$ at $x$, so the deleted node stays allocated and unchanged.
