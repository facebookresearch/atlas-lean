# Truncating overlap-add to the input length fails

Let $Q, N \ge 1$ and $M \ge 2$ be natural numbers, and $L$ any natural number. There are a signal $x$ of length $N$ and a kernel $h$ of length $M$ such that the [overlap-add](overlap-add.md) output $y$ with FFT size $Q$ and hop $L$, cut off at the input length (the function equal to $y(n)$ for $n < N$ and $0$ for $n \ge N$), differs from the [linear convolution](../support-bounded-zero-padding-for-cyclic-convolut/linear-convolution.md) $x * h$. The coefficients of $x * h$ past index $N - 1$ are needed.
