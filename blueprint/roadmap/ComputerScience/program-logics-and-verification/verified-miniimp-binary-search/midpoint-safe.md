# Binary-search midpoint reads are in bounds

For every array `xs` of natural numbers and state `s` with `s hi ≤ xs.size` in which the loop
guard holds (`s lo < s hi`), the midpoint `s lo + (s hi - s lo) / 2` is less
than `xs.size`.
