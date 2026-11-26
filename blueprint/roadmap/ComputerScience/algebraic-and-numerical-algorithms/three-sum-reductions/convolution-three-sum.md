# Convolution-3SUM

**Convolution-3SUM** (three-array form). Given integer arrays $X, Y, Z$ indexed by $\{0, \dots, N-1\}$, decide whether there are indices $i, j$ with $i + j < N$ and

$$
X[i] + Y[j] = Z[i + j].
$$

The one-array version asks for $i, j$ with $a[i] + a[j] = a[i+j]$. Three arrays can be packed into one array of length $O(N)$ with entries enlarged by a constant factor so that solutions correspond.

## Depends on

- [Distinct-position 3SUM](distinct-position-three-sum.md)

## Sources

- T. M. Chan and Q. He, "Reducing 3SUM to Convolution-3SUM", Symposium on Simplicity in Algorithms (SOSA), 2020.
- V. Vassilevska Williams and R. Williams, "Finding, Minimizing, and Counting Weighted Subgraphs", SIAM Journal on Computing 42(3), 2013.
