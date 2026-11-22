# Output of A-star search

An A* result on $n$ vertices consists of a Dijkstra result on $n$
vertices (the underlying search, with its source, final keys and predecessor pointers) and a
vector that assigns to each vertex $v$ a value $g(v) \in \mathbb{N} \cup \{\infty\}$. In the
output of A* from a source $s$ with a consistent heuristic $h$, the underlying search runs on the
reduced weights, its keys are $f(v) - h(s)$ where $f = g + h$, and $g(v)$ is the least weight of
a path from $s$ to $v$, with $\infty$ when there is none.
