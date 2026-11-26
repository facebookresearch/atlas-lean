# Overlap-add block frames are linear convolutions

Let $L, M \ge 1$ and the FFT size $Q \ge L + M - 1$. For a signal $x$ of length $N$, extended by zero ($x_j = 0$ for $j \ge N$, as in a partial last block or a block past the end), a kernel $h$ of length $M$ and any block index $b$, the length-$Q$ cyclic convolution of the block $x_{bL}, \ldots, x_{bL+L-1}$ and the kernel, both zero-padded to length $Q$, read at natural offsets and zero from offset $Q$ on, equals the full linear convolution of that block with $h$ at every offset.
