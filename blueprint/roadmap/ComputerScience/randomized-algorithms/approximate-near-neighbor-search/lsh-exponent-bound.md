# LSH exponent bound rho at most 1/c for linear collision profiles

For $0 < a$ and $c > 1$ with $c a < 1$,

$$
\rho(1 - a, 1 - c a) = \frac{\ln\left(1/(1 - a)\right)}{\ln\left(1/(1 - c a)\right)} \le \frac{1}{c}.
$$

Equivalently $\ln(1 - a) \ge \ln(1 - c a) / c$.

## Proof sketch

The function $\phi(t) = \ln(1 - t)$ is concave on $[0, 1)$ with $\phi(0) = 0$, so $\phi(a) = \phi\left(\frac1c \cdot ca + (1 - \frac1c) \cdot 0\right) \ge \frac1c \phi(ca)$.

## Depends on

- [Locality-sensitive hashing index with L tables and a stopping rule](lsh-index.md)

## Sources

- P. Indyk and R. Motwani, "Approximate Nearest Neighbors: Towards Removing the Curse of Dimensionality", Proceedings of the 30th ACM Symposium on Theory of Computing (STOC), 1998.
- S. Har-Peled, P. Indyk and R. Motwani, "Approximate Nearest Neighbor: Towards Removing the Curse of Dimensionality", Theory of Computing 8(14), 2012.
