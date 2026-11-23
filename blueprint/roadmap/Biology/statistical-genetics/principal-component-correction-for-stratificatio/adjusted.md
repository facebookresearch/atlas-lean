# Residualized vector after adjustment for a subspace

Let $V$ be a linear subspace of $\mathbb{R}^N$ (with the Euclidean inner product) and let $y \in \mathbb{R}^N$. The residual of $y$ after adjustment for $V$ is

$$r_V(y) = y - P_V y,$$

where $P_V$ is the orthogonal projection onto $V$: the residual of the least-squares regression of $y$ on $V$. In EIGENSTRAT, $V$ is the span of the top axes of variation.
