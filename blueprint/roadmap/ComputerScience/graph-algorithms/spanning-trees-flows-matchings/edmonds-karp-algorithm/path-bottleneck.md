# Bottleneck of a path

Let $c$ be a capacity matrix with natural-number entries and $f$
an integer matrix (the flow) on the same vertices. The bottleneck of a list of vertices
$v_0, v_1, \dots, v_k$ with $k \ge 1$ is the integer
$\min_{i < k} \bigl(c(v_i, v_{i+1}) - f(v_i, v_{i+1})\bigr)$, the least residual capacity of a
consecutive pair; a list with at most one vertex has bottleneck $0$.
