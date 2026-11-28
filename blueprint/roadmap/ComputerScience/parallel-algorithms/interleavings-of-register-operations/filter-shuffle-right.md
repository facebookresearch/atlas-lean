# Thread-1 steps of a shuffle

Let $\mathit{tr}_0$, $\mathit{tr}_1$ and $\mathit{trace}$ be traces of thread-tagged operations. Suppose every step of $\mathit{tr}_0$ has a tag different from $1$, every step of $\mathit{tr}_1$ is tagged $1$, and $\mathit{trace}$ is a shuffle of $\mathit{tr}_0$ and $\mathit{tr}_1$ (an interleaving of the two lists that keeps the order within each). Then the steps of $\mathit{trace}$ tagged $1$, in order, are exactly the steps of $\mathit{tr}_1$ tagged $1$.
