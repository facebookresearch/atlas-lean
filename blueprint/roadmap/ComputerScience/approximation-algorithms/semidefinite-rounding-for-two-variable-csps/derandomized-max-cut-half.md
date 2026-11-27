# A deterministic 1/2-approximation for weighted MAX-CUT

For a weighted multigraph on $n$ vertices with edges $(u, v, w)$ of nonnegative weight $w$, assigning the vertices to sides one at a time, each to the side minimizing the expected weight of uncut non-loop edges given the decisions so far (with undecided vertices uniform), yields a cut whose weight is at least half the total weight of non-loop edges, hence at least half the maximum cut. The procedure runs in $O(n + m)$ word-RAM instructions on an edge list.

## Proof sketch

Under a uniform random cut each non-loop edge is cut with probability $1/2$; apply the method of conditional expectations with integer-scaled expected uncut weights.

## Depends on

- [Approximation algorithms and approximation ratios](../approximation-algorithms-and-approximation-ratios.md)
- [The word-RAM model](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [The method of conditional expectations on finite product spaces](method-of-conditional-expectations.md)

## Sources

- D. P. Williamson and D. B. Shmoys, "The Design of Approximation Algorithms", Cambridge University Press, 2011.
- R. Motwani and P. Raghavan, "Randomized Algorithms", Cambridge University Press, 1995.
