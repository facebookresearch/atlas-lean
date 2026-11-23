# Running the binary counter

For a width $k$, a $k$-bit counter $b$ and $n \in \mathbb{N}$,
the run of $n$ increments from $b$ is defined recursively. The run of $0$ increments returns $b$
at cost zero. The run of $n + 1$ increments performs the run of $n$ increments, then increments
the counter it returned and returns the result; its cost is the cost of the $n$-step run plus
the cost of that increment.
