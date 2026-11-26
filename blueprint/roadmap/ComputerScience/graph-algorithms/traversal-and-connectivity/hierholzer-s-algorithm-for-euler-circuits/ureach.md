# Reachability in an undirected multigraph

For a list $E$ of edges (ordered pairs of
vertices), a vertex $x$ is reachable from a vertex $s$ when there are vertices
$s = v_0, v_1, \dots, v_n = x$ with $n \ge 0$ such that for each $i < n$, $(v_i, v_{i+1})$ or
$(v_{i+1}, v_i)$ belongs to $E$.
