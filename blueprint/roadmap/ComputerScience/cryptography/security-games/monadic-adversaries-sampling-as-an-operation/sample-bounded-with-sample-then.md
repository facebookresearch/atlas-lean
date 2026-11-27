# A sampling step costs one unit of sampling budget

Let $i$ be a sampling operation, $k$ a continuation from its outcomes, $\mathsf{cont}$ a predicate on outputs and natural numbers, and $s$ a sampling budget. If, for **every** outcome $b$, the computation $k(b)$ satisfies the [sampling bound](sample-bounded-with.md) with budget $s$ and condition $\mathsf{cont}$, then sampling from operation $i$ and continuing with $k$ ([Sample Then](sample-then.md)) satisfies the sampling bound with budget $s + 1$ and the same condition $\mathsf{cont}$.
