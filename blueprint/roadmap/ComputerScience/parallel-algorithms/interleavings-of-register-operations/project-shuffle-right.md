# Projecting a shuffle onto thread 1

Suppose every step of the trace $\mathit{tr}_0$ has a tag different from $1$, every step of $\mathit{tr}_1$ is tagged $1$, and $\mathit{trace}$ is a shuffle of $\mathit{tr}_0$ and $\mathit{tr}_1$ (an interleaving of the two lists that keeps the order within each). Then the projection of $\mathit{trace}$ onto thread $1$ is the list of operations of $\mathit{tr}_1$, in order (the steps of $\mathit{tr}_1$ with their tags dropped).
