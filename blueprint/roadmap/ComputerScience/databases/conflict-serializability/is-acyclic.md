# A conflict-serializable schedule has an acyclic precedence graph

If a schedule $s$ in
which no operation occurs twice is conflict-serializable, then the precedence graph of $s$ is
acyclic.

In a conflict-equivalent serial schedule, the position of the first operation of each
transaction increases along every edge of the precedence graph.
