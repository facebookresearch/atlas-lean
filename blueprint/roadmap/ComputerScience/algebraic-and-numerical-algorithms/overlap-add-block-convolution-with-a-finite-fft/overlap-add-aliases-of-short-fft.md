# Overlap Add aliases of short fft

Circular aliasing at a short FFT size. Let `Q > 0`, let the signal length `N` be at least the block length `L`, and suppose the block length and the kernel length both fit the FFT size (`L ≤ Q`, `M ≤ Q`) but `Q < L + M - 1`. Then unit impulses at the end of the first block and at the end of the kernel have linear-convolution coefficient `1` at index `L + M - 2` and `0` at index `L + M - 2 - Q`, while overlap-add wraps the coefficient onto index `L + M - 2 - Q` and returns `1` there.
