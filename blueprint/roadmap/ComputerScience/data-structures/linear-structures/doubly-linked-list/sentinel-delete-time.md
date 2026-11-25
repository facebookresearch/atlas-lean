# Sentinel deletion takes two pointer assignments

Let $S$ be a node store and $x$ an
address whose cell holds a node with previous address $p$ and next address $n$, where the cells
at $p$ and $n$ are nonempty. Then sentinel deletion of $x$ from $S$ has cost exactly $2$, one
for each pointer assignment.

This includes the alias cases in which $p$, $n$ and $x$ are not pairwise distinct.
