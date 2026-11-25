# Saved-parent chains are simple

Let $G$ be a finite directed graph given by adjacency
lists and let $s$ and $v$ be vertices. If a list of vertices starts at $s$, ends at $v$, and each
of its vertices after the first has the preceding vertex as its saved parent in the breadth-first
search forest of $G$ from $s$, then no vertex occurs twice in the list.
