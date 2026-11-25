# Sentinel deletion changes only the two neighbours

Let $S$ be a node store and $x$ an
address whose cell holds a node with previous address $p$ and next address $n$, where the cells
at $p$ and $n$ are nonempty. For every address $z$ with $z \ne p$ and $z \ne n$, the cell at $z$
after sentinel deletion of $x$ from $S$ equals the cell of $S$ at $z$.
