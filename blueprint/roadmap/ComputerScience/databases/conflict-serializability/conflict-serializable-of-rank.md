# A rank increasing along precedence edges gives conflict serializability

Let $s$ be a
schedule in which no operation occurs twice. If $r$ is a function from the transactions to the
natural numbers with $r(i) < r(j)$ whenever the precedence graph of $s$ has an edge from $i$ to
$j$, then $s$ is conflict-serializable.
