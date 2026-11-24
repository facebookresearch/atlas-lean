# Sentinel deletion preserves allocation

Let $S$ be a node store and $x$ an address whose
cell holds a node with previous address $p$ and next address $n$, where the cells at $p$ and $n$
are nonempty. For every address $z$, the cell at $z$ after sentinel deletion of $x$ from $S$ is
nonempty if and only if the cell of $S$ at $z$ is nonempty.
