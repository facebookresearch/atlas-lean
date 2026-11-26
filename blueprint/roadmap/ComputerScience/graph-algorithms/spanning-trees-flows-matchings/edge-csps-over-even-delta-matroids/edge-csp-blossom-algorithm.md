# Edge CSPs over even delta-matroids are solvable by a blossom algorithm

For an edge CSP all of whose constraints are even delta-matroids, the algorithm that repeatedly performs one improvement step (a fresh forest search; flip an augmenting walk, or contract a blossom and recurse on the smaller instance, lifting any improvement back) at most one more time than the number of variables returns a valid labeling with the minimum number of defects; it has zero defects exactly when the instance is satisfiable. Each successful improvement removes exactly two defects and each recursion strictly decreases a contraction measure. This generalizes Edmonds' blossom algorithm for perfect matching and underlies the polynomial-time tractability of planar Boolean CSPs over even delta-matroids.

## Proof sketch

Termination: defects decrease by two per successful improvement and contraction decreases the instance. Correctness: the augmentation lemma, the blossom contraction lemma, and the optimality of an exhausted search.

## Depends on

- [Edge CSPs, occurrence labelings and defects](edge-csps-and-defects.md)
- [General matching is in P (Edmonds' blossom algorithm)](../../../../TheoryOfComputation/polynomial-time-problems/matching-in-general-graphs/matching-in-p.md)

## Proof depends on

- [Augmenting walks remove two defects](edge-csp-augmenting-walks.md)
- [Blossom contraction preserves improvability](edge-csp-blossom-contraction.md)
- [An exhausted forest search certifies optimality](edge-csp-exhausted-search-optimality.md)

## Sources

- A. Kazda, V. Kolmogorov and M. Rolínek, "Even Delta-Matroids and the Complexity of Planar Boolean CSPs", ACM Transactions on Algorithms 15(2), 2019.
