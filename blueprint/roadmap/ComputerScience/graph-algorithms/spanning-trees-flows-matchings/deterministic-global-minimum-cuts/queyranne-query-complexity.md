# Exact value-oracle complexity of Queyranne's algorithm

Run against an arbitrary value oracle for $f$ on $n \ge 2$ elements, Queyranne's algorithm makes exactly $Q$ value queries where

$$
6Q + 12n = n(n+1)(n+2) + 6,
$$

so $Q = \Theta(n^3)$; for $n < 2$ it makes one query. The count does not depend on the oracle's answers.

## Proof sketch

The $k$-th of the $n - 1$ rounds builds an MA ordering over $n - k + 1$ classes, querying $f$ once per candidate per step plus once for the recorded class; summing gives the cubic polynomial.

## Depends on

- [Queyranne's algorithm minimizes symmetric submodular functions](queyranne-algorithm.md)
- [Value and independence oracle models](../../../greedy-algorithms-and-matroids/submodular-maximization-and-oracle-complexity/value-and-independence-oracle-models.md)

## Sources

- M. Queyranne, "Minimizing Symmetric Submodular Functions", Mathematical Programming 82, 1998.
