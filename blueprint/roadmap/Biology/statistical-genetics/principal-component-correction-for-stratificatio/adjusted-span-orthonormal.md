# Residual with respect to an orthonormal family of axes

Let $a_1, \dots, a_K \in \mathbb{R}^N$ be orthonormal and let $y \in \mathbb{R}^N$. Then the [residual](adjusted.md) of $y$ after adjustment for the span of $a_1, \dots, a_K$ is

$$r(y) = y - \sum_{k=1}^{K} \langle a_k, y \rangle\, a_k,$$

so regressing on the axes one at a time gives the joint residual.
