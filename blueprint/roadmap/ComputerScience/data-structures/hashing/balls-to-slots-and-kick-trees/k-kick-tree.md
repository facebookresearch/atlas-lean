# k-kick tree balls-to-slots scheme

A *$k$-kick tree* over $M$ slots organizes the slots into a hierarchy of depths $0, 1, \dots, k$: at depth $0$ there is one bin spanning all slots, and deeper levels partition the slots into smaller power-of-two bins. Each ball receives, from its hash, a bin at every depth and a random *depth cap*, with the probability of a large cap decreasing geometrically. A ball is inserted into a free slot of its depth-$0$ bin if possible; otherwise it *kicks* a ball of lower priority out of a deeper bin, and the kicked ball is reinserted one level deeper, at most $k$ times. Deletion only vacates the deleted ball's slot.

## Depends on

- [Balls-to-slots problem and probe complexity](balls-to-slots-problem.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul and M. Liu, "On the Optimal Time/Space Tradeoff for Hash Tables", Proceedings of the 54th ACM Symposium on Theory of Computing (STOC), 2022; arXiv:2111.00602.
