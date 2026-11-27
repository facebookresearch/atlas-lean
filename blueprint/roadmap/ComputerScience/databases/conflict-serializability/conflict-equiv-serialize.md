# Serializing along a topological order preserves conflict equivalence

Let $s$ be a
schedule in which no operation occurs twice, and let $L$ be a topological order of the
precedence graph of $s$. Then the schedule obtained from $s$ by stably sorting its operations
by the first position of their transaction in $L$ is conflict-equivalent to $s$.
