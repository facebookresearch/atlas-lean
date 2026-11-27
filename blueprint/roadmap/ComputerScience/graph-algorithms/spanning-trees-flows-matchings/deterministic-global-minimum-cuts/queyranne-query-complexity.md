# Exact value-oracle complexity of Queyranne's algorithm

Queyranne's algorithm minimizes a symmetric submodular function $f$ on a ground set $V$ with $|V| = n \ge 2$ using $O(|V|^3)$ value-oracle calls: each of its $n - 1$ rounds builds a maximum adjacency (legal) ordering, starting from an arbitrary element, with $O(|V|^2)$ calls, and then contracts the resulting pendant pair (Queyranne; Goemans and Soto, Section 1 and Section 2, Lemma 3).

## Proof sketch

Fix the following query schedule, where a set of current classes is evaluated as the union of their elements; its query count is $\Theta(|V|^3)$ and does not depend on the oracle's answers. In a round with $m$ classes, the MA ordering starts from a class $v_1$ fixed in advance (the least in a fixed order of the classes), the value $f(\{v\})$ is queried once for each of the other $m - 1$ classes, and at each step with at least two candidates $f(A \cup \{v\})$ is queried for every candidate $v$, where $A$ is the set of classes already ordered; at the last step the only candidate is taken without a query, and the recorded value $f(\{t\})$ of the merged class of $t$ reuses its singleton query. A round with $m$ classes then makes $m - 1$ singleton queries and, at its $m - 2$ steps with at least two candidates, $\sum_{c=2}^{m-1} c = m(m-1)/2 - 1$ further queries, so $m(m+1)/2 - 2$ in total, whatever the oracle answers. Summing over $m = n, n - 1, \dots, 2$ gives exactly $Q = n(n+1)(n+2)/6 - 1 - 2(n-1)$ queries, that is,

$$
6Q + 12n = n(n+1)(n+2) + 6,
$$

so $Q = \Theta(n^3)$; for example $Q = 1$ for $n = 2$ and $Q = 5$ for $n = 3$.

## Depends on

- [Queyranne's algorithm minimizes symmetric submodular functions](queyranne-algorithm.md)
- [Maximum adjacency orderings](maximum-adjacency-ordering.md)
- [Value and independence oracle models](../../../greedy-algorithms-and-matroids/submodular-maximization-and-oracle-complexity/value-and-independence-oracle-models.md)

## Sources

- M. Queyranne, "Minimizing Symmetric Submodular Functions", Mathematical Programming 82, 1998.
- M. X. Goemans and J. A. Soto, "Algorithms for Symmetric Submodular Function Minimization under Hereditary Constraints and Generalizations", SIAM Journal on Discrete Mathematics 27(2), 2013; preprint "Symmetric Submodular Function Minimization Under Hereditary Family Constraints", arXiv:1007.2140, 2010, Section 1 and Section 2, Lemma 3.
