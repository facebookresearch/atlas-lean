# Probe complexity of k-kick trees under 3-wise independence

For the standard $k$-kick tree with $2^{m_0}$ slots and a 3-wise independent hash function:

1. every insertion moves at most $k + 1$ balls (switching cost at most $k+1$), deterministically;
2. inserting a new ball into a valid configuration holding fewer than $2^{m_0}$ balls gives it expected probe complexity $O(\max(\log^{(k+1)} 2^{m_0}, 1))$;
3. over any valid operation history fixed in advance, the expected total probe complexity is $O(|A| \max(\log^{(k+1)} 2^{m_0}, 1))$, where $A$ is the set of balls present at the end.

With $O(m)$-wise independence and a partition of the history into sub-histories with disjoint footprints, the total probe complexity also concentrates around this bound with polynomially small tail probability (via a $2m$-th moment bound).

## Proof sketch

A ball ends at depth $d$ only if it was kicked $d$ times, which requires its bins at depths $0, \dots, d-1$ to be full; under 3-wise independence the probability of each kick is small enough that the expected index of a ball's final slot inside its probe sequence is bounded by an iterated exponential, whose logarithm is the iterated logarithm. Linearity of expectation over the present balls gives the total bound.

## Depends on

- [k-kick tree balls-to-slots scheme](k-kick-tree.md)
- [k-wise independent hash family](../word-ram-hash-families/k-wise-independent-hash-family.md)
- [Iterated logarithm and log-star](../dictionary-specifications/iterated-logarithm.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul and M. Liu, "On the Optimal Time/Space Tradeoff for Hash Tables", Proceedings of the 54th ACM Symposium on Theory of Computing (STOC), 2022; arXiv:2111.00602.
