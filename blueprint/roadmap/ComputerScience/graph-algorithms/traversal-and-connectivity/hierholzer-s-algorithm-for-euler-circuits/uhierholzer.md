# Undirected Hierholzer's algorithm

Given a list $E$ of undirected edges (ordered pairs of
vertices) and a start vertex $s$, run the undirected Hierholzer recursion from $s$ on $E$ with an
empty accumulator and fuel $|E| + 1$, and return the list of emitted vertices; its cost is the
cost of that recursion.
