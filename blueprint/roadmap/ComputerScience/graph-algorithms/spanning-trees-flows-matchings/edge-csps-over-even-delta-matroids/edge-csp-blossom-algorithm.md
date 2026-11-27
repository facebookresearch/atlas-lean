# Edge CSPs over even delta-matroids are solvable by a blossom algorithm

For an edge CSP all of whose constraints are nonempty even delta-matroids, start from any valid labeling (one tuple chosen per constraint) and repeat the improvement step: run a fresh forest search (which reports a meeting of two branches whenever a variable reached through a new copy of a constraint $C$ is already in the forest, unless its parent is a copy of the same constraint $C$), and either flip an augmenting walk, or contract a blossom, recurse on the contracted instance and lift any improvement back, or stop when the search is exhausted. Each successful step removes at least two defects (exactly two for a direct augmentation), so after at most one more step than the number of variables the algorithm stops, and it returns an optimal valid labeling; the instance is satisfiable exactly when that labeling has no defects. A chain of nested contractions has length at most twice the number of variables, since each contraction adds one constraint, never adds variables, and an edge CSP with $n$ variables has at most $2n$ constraints with nonempty scope. The whole computation takes time polynomial in the size of the instance. This generalizes Edmonds' blossom algorithm for perfect matching and underlies the polynomial-time tractability of planar Boolean CSPs over even delta-matroids.

## Proof sketch

Termination: the number of defects is at most the number of variables, all valid labelings have the same parity of defects, and each successful step strictly decreases it; nested contractions are bounded as stated, and each contraction enlarges the instance by $O(n)$ tuples. Correctness: the augmentation lemma, the blossom contraction lemma, and the optimality of an exhausted search, by induction on the nesting depth of contractions.

## Depends on

- [Edge CSPs, occurrence labelings and defects](edge-csps-and-defects.md)
- [Delta-matroids and even delta-matroids](../../../../TheoryOfComputation/np-completeness/boolean-constraint-satisfaction/planar-boolean-csp/delta-matroids-and-even-delta-matroids.md)
- [General matching is in P (Edmonds' blossom algorithm)](../../../../TheoryOfComputation/polynomial-time-problems/matching-in-general-graphs/matching-in-p.md)
- [Augmenting walks remove two defects](edge-csp-augmenting-walks.md)
- [Blossom contraction preserves improvability](edge-csp-blossom-contraction.md)

## Proof depends on

- [An exhausted forest search certifies optimality](edge-csp-exhausted-search-optimality.md)

## Sources

- A. Kazda, V. Kolmogorov and M. Rolínek, "Even Delta-Matroids and the Complexity of Planar Boolean CSPs", ACM Transactions on Algorithms 15(2), Article 22, 2019, Theorem 21, Theorem 24, Corollary 27, Corollary 46 and Section 5.4.
