# Kahn's topological sort

Run Kahn's algorithm with a first-in first-out queue on a finite
directed graph $G$ whose vertices are enumerated as $v_1, \dots, v_n$. Initially every vertex is
remaining, the counter of each vertex is its number of in-neighbours, and the queue holds the
vertices with no in-neighbours in enumeration order. At each of $n$ steps, if the queue is nonempty,
its front vertex $x$ is removed from the queue and from the remaining vertices and appended to the
output; then each distinct out-neighbour $y$ of $x$ that is still remaining, taken in order of first
occurrence in the adjacency list of $x$, has its counter decreased by one and joins the back of the
queue if that counter was $1$. If no vertices remain after the $n$ steps, the result is a success
with the output list; otherwise it is a failure with the output list as the processed vertices and
the remaining vertices in enumeration order.
