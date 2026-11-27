# A rank lower bound from two trace moments

For every real matrix $A$ with Gram matrix $H=A^{T}A$,

$$
(\operatorname{tr}H)^2\le\operatorname{rank}(A)\cdot\operatorname{tr}(H^2),
$$

so $\operatorname{rank}A\ge(\operatorname{tr}A^TA)^2/\operatorname{tr}\bigl((A^TA)^2\bigr)$ whenever $A\neq0$.

## Proof sketch

$H$ is symmetric positive semidefinite of rank $\operatorname{rank}A$; its trace is the sum of its nonzero eigenvalues and $\operatorname{tr}H^2$ is the sum of their squares, so Cauchy–Schwarz over the $\operatorname{rank}A$ nonzero eigenvalues gives the inequality.

## Sources

- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
