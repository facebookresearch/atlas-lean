# A sampling step is free for the oracle budget

Let $i$ be a sampling operation, $k$ a continuation from its outcomes, $\mathsf{cont}$ a predicate on outputs and natural numbers, and $q$ a query budget. If, for **every** outcome $b$, the computation $k(b)$ satisfies the oracle bound ([Oracle Bounded With](oracle-bounded-with.md)) with budget $q$ and condition $\mathsf{cont}$, then sampling from operation $i$ and continuing with $k$ ([Sample Then](sample-then.md)) satisfies the oracle bound with the same budget $q$ and the same condition $\mathsf{cont}$.
