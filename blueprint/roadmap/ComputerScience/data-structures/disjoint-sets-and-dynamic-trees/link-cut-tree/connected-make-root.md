# Making a vertex the root keeps its connections

Let $s$ be a valid link-cut tree state
and let $x$ and $y$ be connected in $s$. Then $x$ and $y$ are still connected in the state
obtained from $s$ by making $x$ the root of its represented tree.

Rerooting spans the same vertex set as the old tree and keeps every undirected edge; vertex
disjointness of the represented trees pins down which tree contains $x$.
