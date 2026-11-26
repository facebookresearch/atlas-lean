# Entries of the sample covariance matrix

For random vectors $X_1, \dots, X_N \in \mathbb{R}^d$ and an outcome $\omega$, entry $(j, k)$ of the sample covariance of the data matrix whose rows are $X_i(\omega)$ is $\frac{1}{N-1} \sum_i (X_{ij} - \bar X_j)(X_{ik} - \bar X_k)$, where $\bar X_j = \frac1N \sum_l X_{lj}$. For $N = 1$ the factor $1/(N - 1)$ is $0$ by the convention for the inverse of zero, and for an empty sample ($N = 0$) the coordinate means and the entry are $0$.
