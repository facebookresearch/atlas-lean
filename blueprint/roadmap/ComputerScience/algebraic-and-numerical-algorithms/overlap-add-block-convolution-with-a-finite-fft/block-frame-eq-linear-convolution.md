# Overlap-add block frames are linear convolutions

Let $L, M \ge 1$ and the FFT size $Q \ge L + M - 1$. For a signal $x$ of length $N$, a kernel $h$ of length $M$ and any block index $b$, the length-$Q$ cyclic convolution of the zero-padded block $x_{bL}, \ldots, x_{bL+L-1}$ with the zero-padded kernel, extended by zero beyond $Q$, equals the full linear convolution of that block with $h$.
