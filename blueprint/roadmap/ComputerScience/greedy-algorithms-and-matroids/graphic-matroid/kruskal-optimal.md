# Optimality of Kruskal's algorithm

Let $G$ be a simple graph on a finite vertex type
$V$, let $w$ assign a natural number to each unordered pair of vertices, and let $L$ be a list
of unordered pairs of vertices in nonincreasing order of $w$ (each entry weighs at least as much
as every later one). Let $T$ be the set returned by the matroid greedy algorithm run on $L$ with
the forest oracle of $G$. Then every forest $I$ of $G$ all of whose edges occur in $L$ satisfies
$\sum_{x \in I} w(x) \le \sum_{x \in T} w(x)$.

This is CLRS Theorem 16.11 on the graphic matroid.
