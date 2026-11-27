# The Gale-Shapley matching

Let $n \in \mathbb{N}$, and let each of $n$ proposers and each of $n$ receivers rank the other
side by a bijection of $\{0, \dots, n - 1\}$ (the image of $k$ is the choice of rank $k$, rank
$0$ being the best). Run deferred acceptance from the initial state (no proposals made, no
proposer held) for at most $n^2$ proposals, which always suffices for it to terminate. The
Gale-Shapley matching is the perfect matching that pairs each proposer with the receiver who holds
him in the final state.
