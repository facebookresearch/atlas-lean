# Cost of the transition stages of transitive closure

Charge one time unit for each cell
assignment. For every Boolean adjacency matrix on $n$ vertices, let $a$ be the cost of running the
initialization of the saved-matrix transitive-closure algorithm followed by all $n$ of its
stages, and let $b$ be the cost of running the initialization alone. Then $a - b = n^3$, where the
subtraction is subtraction of natural numbers, truncated at $0$. That is, the $n$ transition
stages together perform exactly $n^3$ cell assignments.
