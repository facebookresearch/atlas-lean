# Balls-to-slots problem and probe complexity

In the *balls-to-slots* problem a dynamic set of balls from a universe is maintained in $M$ slots under insertions and deletions, each ball occupying one slot. Each ball $x$ has a fixed *probe sequence* $p_x(0), p_x(1), \dots$ of slots determined by hashing. If $x$ sits in slot $p_x(i)$, its *probe complexity* is $1 + \lfloor \log_2 (i + 1) \rfloor$ (the cost of describing $i$ in a self-delimiting way); the total probe complexity of a configuration is the sum over present balls. The *switching cost* of an operation is the number of balls that move. A scheme with total probe complexity $P$ yields a hash table whose wasted space is about $P$ bits.

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul and M. Liu, "On the Optimal Time/Space Tradeoff for Hash Tables", Proceedings of the 54th ACM Symposium on Theory of Computing (STOC), 2022; arXiv:2111.00602.
