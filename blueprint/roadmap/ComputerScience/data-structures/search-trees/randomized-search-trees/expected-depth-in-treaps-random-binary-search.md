# Expected depth in treaps, random binary search trees and skip lists

Let $1 \le k \le n$. In a treap on keys $1 < \cdots < n$ whose priorities are independent and drawn from a common continuous distribution, so that ties occur with probability zero and the priority order is a uniformly random permutation, equivalently a binary search tree built by inserting the keys in uniformly random order, the expected depth of the $k$-th key is $H_k + H_{n-k+1} - 2$, where $H_j$ is the $j$-th harmonic number and the root has depth $0$, and the expected height is $O(\log n)$. In a skip list on $n$ keys in which each key independently appears on levels $1, \dots, h$ with $\Pr[h \ge i] = 2^{-(i-1)}$, the expected number of pointer steps of a search, proceeding from the top level downward, is $O(\log n)$.

## Depends on

- [Expected running time](../../../randomized-algorithms/average-case-running-time/expected-time.md)
- [Valid treap](../treap/valid.md)

## Expansion

This page becomes ready once:

- Dictionary and ordered-set abstract data types (statement prerequisite; formal statement exists, page pending)
- Expected depth in treaps and random binary search trees, as a page of its own
- Expected search cost in skip lists, as a page of its own

## Sources

- R. Seidel and C. R. Aragon, "Randomized search trees", *Algorithmica* 16(4–5):464–497, 1996
- W. Pugh, "Skip lists: a probabilistic alternative to balanced trees", *Communications of the ACM* 33(6):668–676, 1990
