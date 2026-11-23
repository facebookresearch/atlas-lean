# Sum count Ico eq length

Counting blocks by size over `[1, n)` counts every block once: if a list of
block sizes has positive entries summing to `n` and at least two blocks, every
entry lies in `[1, n - 1]`, so `∑_{i=1}^{n-1} #{blocks of size i}` is the number
of blocks.
