# Logged run of a monadic computation

Fix types $X$ of queries and $Y$ of answers, a sampling family and a randomized oracle $O$ from $X$ to distributions on $Y$. The logged run maps a single-oracle computation with sampling to a distribution on pairs $(a, \ell)$, where $a$ is the result and $\ell$ the ordered list of (query, answer) pairs:

- a computation returning $a$ at once gives the point mass at $(a, [\,])$;
- a sampling step $i$ draws $b$ from the family's distribution for $i$ and continues; it is **not** recorded;
- a query $x$ draws $y \leftarrow O(x)$, continues, and prepends $(x, y)$ to the log of the continuation.

Forgetting the log gives the output distribution ([M Eval Log map fst](m-eval-log-map-fst.md)). This is the monadic form of the logged run of a single-oracle computation.
