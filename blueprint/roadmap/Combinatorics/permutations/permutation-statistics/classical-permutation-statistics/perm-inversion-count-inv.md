# A permutation and its inverse have the same number of inversions

For every permutation $\sigma$ of $\{0, \dots, n-1\}$, $\mathrm{inv}(\sigma^{-1}) = \mathrm{inv}(\sigma)$.
The pair of positions $(i, j)$ is an [inversion](perm-inversions.md) of $\sigma$ exactly when the
pair $(\sigma(j), \sigma(i))$ is an inversion of $\sigma^{-1}$, and this is a bijection between the
two sets of inversions. This is Proposition 1.3.14 of Stanley's book.

## Sources

- Richard P. Stanley, *Enumerative Combinatorics*, Vol. 1, 2nd ed., Cambridge University Press,
  2012, Section 1.3: https://math.mit.edu/~rstan/ec/ec1.pdf, Proposition 1.3.14.
