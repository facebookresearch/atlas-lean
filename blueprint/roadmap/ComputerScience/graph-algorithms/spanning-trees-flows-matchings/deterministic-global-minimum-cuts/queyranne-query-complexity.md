# Exact value-oracle complexity of Queyranne's algorithm

Implement Queyranne's algorithm on $n \ge 2$ elements with the following query schedule, where a set of current classes is evaluated as the union of their elements. In a round with $m$ classes, the MA ordering starts from a class $v_1$ fixed in advance (the least in a fixed order of the classes), the value $f(\{v\})$ is queried once for each of the other $m - 1$ classes, and at each step with at least two candidates $f(A \cup \{v\})$ is queried for every candidate $v$, where $A$ is the set of classes already ordered; at the last step the only candidate is taken without a query, and the recorded value $f(\{t\})$ of the merged class of $t$ reuses its singleton query. Run against an arbitrary value oracle for $f$, this implementation makes exactly $Q$ value queries where

$$
6Q + 12n = n(n+1)(n+2) + 6,
$$

so $Q = \Theta(n^3)$, within the $O(|V|^3)$ oracle calls of Queyranne's theorem. The count does not depend on the oracle's answers.

## Proof sketch

A round with $m$ classes makes $m - 1$ singleton queries and, at its $m - 2$ steps with at least two candidates, $\sum_{c=2}^{m-1} c = m(m-1)/2 - 1$ further queries, so $m(m+1)/2 - 2$ in total. Summing over $m = n, n - 1, \dots, 2$ gives $Q = n(n+1)(n+2)/6 - 1 - 2(n-1)$, which is the formula; for example $Q = 1$ for $n = 2$ and $Q = 5$ for $n = 3$.

## Depends on

- [Queyranne's algorithm minimizes symmetric submodular functions](queyranne-algorithm.md)
- [Maximum adjacency orderings](maximum-adjacency-ordering.md)
- [Value and independence oracle models](../../../greedy-algorithms-and-matroids/submodular-maximization-and-oracle-complexity/value-and-independence-oracle-models.md)

## Sources

- M. Queyranne, "Minimizing Symmetric Submodular Functions", Mathematical Programming 82, 1998.
