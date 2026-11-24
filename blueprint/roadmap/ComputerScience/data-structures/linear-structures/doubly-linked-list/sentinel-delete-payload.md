# Sentinel deletion preserves payloads

Let $S$ be a node store and $x$ an address whose
cell holds a node with previous address $p$ and next address $n$, where the cells at $p$ and $n$
are nonempty. For every address $z$, the cell at $z$ after sentinel deletion of $x$ from $S$
and the cell of $S$ at $z$ are either both empty or both hold nodes with the same payload.

The payload includes any key and satellite data.
