# Executions agree while deliveries agree

Let $Q$ be a [synchronous protocol with crash failures](crash-protocol.md), $x$ an assignment of inputs, $\pi$, $\pi'$ [crash patterns](crash-pattern.md) and $k \in \mathbb{N}$. If in every round $r < k$ the [deliveries](delivers.md) of $\pi$ and $\pi'$ agree (for all senders and recipients), then for every $r \le k$ every process is in the same [state](state.md) after $r$ rounds under $\pi$ as under $\pi'$.
