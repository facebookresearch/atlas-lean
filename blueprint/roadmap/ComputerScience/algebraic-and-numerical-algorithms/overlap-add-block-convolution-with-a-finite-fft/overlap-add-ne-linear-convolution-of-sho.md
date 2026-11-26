# Overlap-add with a short FFT size fails

Let $L, M \ge 1$, $N \ge L$ and $1 \le Q < L + M - 1$ be natural numbers. There are a signal $x$ of length $N$ and a kernel $h$ of length $M$ such that the [overlap-add](overlap-add.md) output with FFT size $Q$ and hop $L$ differs from the [linear convolution](../support-bounded-zero-padding-for-cyclic-convolut/linear-convolution.md) $x * h$.

Two mechanisms occur. When $Q < L$ or $Q < M$, [zero extension](../support-bounded-zero-padding-for-cyclic-convolut/zero-extend.md) to length $Q$ keeps only the first $Q$ entries of a block or of the kernel, so input is lost before the cyclic convolution (for example $N = L = 2$, $M = Q = 1$). When $L \le Q$ and $M \le Q$ the failure is [circular aliasing](overlap-add-aliases-of-short-fft.md).
