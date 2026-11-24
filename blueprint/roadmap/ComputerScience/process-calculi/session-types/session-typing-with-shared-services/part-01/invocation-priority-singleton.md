# Invocation priority for a singleton of rank above the priority

Let $\sigma = (\pi, r, c_0)$ be a service signature, $e$ an endpoint and $c$ a capability whose rank
is strictly greater than $\pi$. Then the invocation priority condition holds for $\sigma$ and $\{e
\mapsto c\}$: $\pi$ is below the rank of every active capability of $\{e \mapsto c\}$.
