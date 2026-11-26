# Thread-0 steps of a shuffle are the thread-0 trace

Let $\mathit{tr}_0$, $\mathit{tr}_1$ and $\mathit{trace}$ be traces of thread-tagged operations. Suppose every step of $\mathit{tr}_0$ is tagged $0$, every step of $\mathit{tr}_1$ has a tag different from $0$, and $\mathit{trace}$ is a shuffle of $\mathit{tr}_0$ and $\mathit{tr}_1$ (an interleaving of the two lists that keeps the order within each). Then the steps of $\mathit{trace}$ tagged $0$, in order and with their tags, are exactly $\mathit{tr}_0$.
