# Dp

The approximate-matching dynamic-programming matrix: `dp P T 0 j = 0`,
`dp P T i 0 = i`, and `dp P T (i+1) (j+1)` is the minimum of `dp P T i (j+1) + 1`,
`dp P T (i+1) j + 1` and `dp P T i j` plus `0` if `P[i] = T[j]` and `1` otherwise.
