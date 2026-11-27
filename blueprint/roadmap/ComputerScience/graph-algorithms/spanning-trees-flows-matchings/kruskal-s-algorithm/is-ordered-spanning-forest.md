# Ordered spanning forest

For an input graph $G$ on the vertices $\{0, \dots, n-1\}$,
a list $e_1, \dots, e_k$ of validated edges is an ordered spanning forest of $G$ when it is a
spanning forest of $G$ and its keys are nondecreasing: for all $i < j$, the key of $e_i$ is
at most the key of $e_j$, where the key of an edge with weight $w$ and input ordinal $o$ is
the pair $(w, o)$ and keys are compared lexicographically.
