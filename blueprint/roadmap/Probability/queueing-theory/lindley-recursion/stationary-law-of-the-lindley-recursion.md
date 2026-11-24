# The supremum of the random walk is a stationary law of Lindley's recursion

Let $X_1, X_2, \dots$ be i.i.d. with partial sums $S_k$ and $M_\infty = \sup_{k \ge 0} S_k$, and suppose $M_\infty$ is almost surely finite. If $W$ has the law of $M_\infty$ and $X$ is independent of $W$ with the law of $X_1$, then $\max(0, W + X)$ again has the law of $M_\infty$: the law of $M_\infty$ is a stationary distribution of Lindley's recursion $W_{n+1} = \max(0, W_n + X_{n+1})$.

Proof. With $M' = \sup_{k \ge 0}(X_2 + \dots + X_{k+1})$, independent of $X_1$ and distributed as $M_\infty$, $\max(0, X_1 + M') = \max(0, \sup_{k \ge 1} S_k) = M_\infty$. Stationary versions for stationary ergodic, not necessarily independent, increments (Loynes' construction) are a separate statement.

## Background

- [Lindley's recursion and the maximum of the random walk](lindley-recursion-and-the-maximum-of-the-reversed-walk.md): the laws of $W_n$ increase to the law of $M_\infty$.

## Expansion

- A primary source that states this result in the form given here is to be located and checked before the statement is relied on.
