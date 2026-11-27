# The Hungarian method in O(n^3) word-RAM time

There is a deterministic word-RAM program implementing the slack-array Kuhn-Munkres method that, given an $n \times n$ matrix of integer costs, returns a minimum-cost perfect matching (assignment) together with integral dual potentials whose sum equals its cost, within $O(n^3)$ instructions at every word size holding $n$ times the cost range.

## Proof sketch

Grow one alternating tree per row; maintaining for each unused column the minimum slack makes each dual adjustment and tree extension $O(n)$, with at most $n$ extensions per row.

## Depends on

- [Correctness of the Hungarian algorithm](../hungarian-algorithm.md)
- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Dual certificate for the assignment problem](../dual-certificate-for-the-assignment-problem.md)

## Sources

- H. W. Kuhn, "The Hungarian Method for the Assignment Problem", Naval Research Logistics Quarterly 2, 1955.
- J. Munkres, "Algorithms for the Assignment and Transportation Problems", Journal of the Society for Industrial and Applied Mathematics 5(1), 1957.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd ed., MIT Press, 2009.
