# The last overlap-add block starts inside the signal

For natural numbers $N \ge 1$ and $L \ge 1$, the [block count](block-count.md) satisfies

$$(B(N, L) - 1) \cdot L < N.$$

So the last block, which starts at $(B(N, L) - 1) L$, contains a sample of the signal. For $N = 0$ there are no blocks ($B(0, L) = 0$) and no last block.
