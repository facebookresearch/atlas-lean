# Circular aliasing of overlap-add at a short FFT size

Let $Q \ge 1$, $N$, $L$ and $M$ be natural numbers with $L \le N$, $L \le Q$, $M \le Q$ and $Q < L + M - 1$. There are a signal $x$ of length $N$ and a kernel $h$ of length $M$ such that, with $y$ the [overlap-add](overlap-add.md) output with FFT size $Q$ and hop $L$ and $*$ [linear convolution](../support-bounded-zero-padding-for-cyclic-convolut/linear-convolution.md),

$$(x * h)(L + M - 2) = 1, \qquad (x * h)(L + M - 2 - Q) = 0, \qquad y(L + M - 2 - Q) = 1.$$

Unit impulses at the end of the first block and at the end of the kernel serve: their last linear coefficient, at index $L + M - 2$, wraps onto index $L + M - 2 - Q$.
