# Projecting a shuffle onto thread 0

Suppose every step of the trace $\mathit{tr}_0$ is tagged $0$, every step of $\mathit{tr}_1$ has a tag different from $0$, and $\mathit{trace}$ is a shuffle of $\mathit{tr}_0$ and $\mathit{tr}_1$ (an interleaving of the two lists that keeps the order within each). Then the projection of $\mathit{trace}$ onto thread $0$ is the list of operations of $\mathit{tr}_0$, in order (the steps of $\mathit{tr}_0$ with their tags dropped).
