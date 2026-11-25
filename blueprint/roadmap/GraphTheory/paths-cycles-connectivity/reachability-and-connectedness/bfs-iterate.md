# Breadth-first search with a round limit

For a simple graph $G$ on a finite vertex set,
a natural number $n$ and a set $s$ of vertices, this applies rounds of breadth-first search to
$s$ (each round adds all neighbours of the current vertices), stopping after $n$ rounds or as
soon as a round adds no new vertex, whichever comes first, and returns the resulting set.
