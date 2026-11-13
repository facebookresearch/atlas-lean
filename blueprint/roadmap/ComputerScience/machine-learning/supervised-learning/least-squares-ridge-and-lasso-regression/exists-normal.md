# Least-squares estimates exist

Let $X$ be a real matrix with $m$ rows and columns indexed
by a finite set $\iota$, and let $y \in \mathbb{R}^m$. Then there is $\theta \in \mathbb{R}^\iota$
with $X^\top X \theta = X^\top y$: the normal equations always have a solution, whatever the rank
of $X$.

The reason is that the range of $X^\top X$ is contained in that of $X^\top$ and the two matrices
have the same rank, so their ranges coincide.
