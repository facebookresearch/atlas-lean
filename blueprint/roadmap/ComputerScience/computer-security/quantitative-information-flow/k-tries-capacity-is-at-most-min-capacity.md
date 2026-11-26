# Capacity with k tries is at most min-capacity

**Corollary.** For every channel $C$ and every $k \ge 1$, the capacity of $C$ under the [$k$-tries gain function](binary-partition-and-k-tries-gain-functions.md), the supremum over priors of
its g-leakage, is at most the [min-capacity](g-leakage-and-g-capacity.md) $ML(C)$. Allowing more guesses raises prior and posterior vulnerability but not capacity.

## Depends on

- [Binary, partition and k-tries gain functions](binary-partition-and-k-tries-gain-functions.md)
- [g-leakage and g-capacity](g-leakage-and-g-capacity.md)

## Proof depends on

- [Miracle theorem](miracle-theorem.md)

## Sources

- M. S. Alvim, K. Chatzikokolakis, C. Palamidessi and G. Smith, "Measuring information leakage using generalized gain functions", *Proceedings of the 25th IEEE Computer Security Foundations Symposium (CSF 2012)*, copy at <https://www.chatzi.org/papers/csf12_gleakage.pdf>: Section V-A, Corollary 5.2 and its proof.
