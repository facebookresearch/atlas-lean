# Minimum weight of a walk with $k$ edges

For a list of weighted edge occurrences, vertices $s$ and $v$ and a natural number $k$, an integer $x$ is the minimum weight of a walk with $k$ edges from $s$ to $v$ when some walk ("edge progression") with exactly $k$ edges from $s$ to $v$ has weight $x$ and none has a smaller weight. This is Karp's $F_k(v) = x$; when there is no such walk, $F_k(v) = \infty$ and no $x$ qualifies. Walks may repeat vertices and edges.

## Sources

- R. M. Karp, "A characterization of the minimum cycle mean in a digraph", *Discrete Mathematics* 23(3) (1978), 309–311, Theorem 1 and Lemma 2.
