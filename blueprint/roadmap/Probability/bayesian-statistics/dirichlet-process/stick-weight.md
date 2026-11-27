# Stick-breaking weights

For proportions $b = (b_0, b_1, \dots)$ of real numbers and $k \in \mathbb{N}$, the $k$-th piece of a stick of length $1$ broken at proportions $b$ is

$$\pi_k(b) = b_k \prod_{j<k} (1 - b_j) = b_k\, R_k(b),$$

where $R_k(b)$ is the [leftover stick](stick-remainder.md). Indices start at $0$, so $\pi_k$ is $p_{k+1}$ in Sethuraman's notation.
