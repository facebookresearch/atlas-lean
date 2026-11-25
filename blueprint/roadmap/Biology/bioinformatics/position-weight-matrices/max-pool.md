# Global max pooling

For a filter $W$, a sequence $x$ and a natural number $m$ (a sequence of length $m + w$), the max-pooled output is $\max_{0 \le i \le m} \mathrm{conv}_W(x, i)$, where $\mathrm{conv}$ is the [response](conv.md).
