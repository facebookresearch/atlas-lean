# Convolution-3SUM

**Convolution-3SUM** (three-array form). Given integer arrays $X, Y, Z$ indexed by $\{0, \dots, N-1\}$, decide whether there are indices $i, j$ with $i + j < N$ and

$$
X[i] + Y[j] = Z[i + j].
$$

The one-array version asks for $i, j$ with $a[i] + a[j] = a[i+j]$. Three arrays reduce to one: with $B = \max_i \max(|X[i]|, |Y[i]|, |Z[i]|)$ and $T = 3B + 1$, the array $a$ of length $4N$ with $a[4i+1] = X[i] + T$, $a[4i+2] = Y[i] + 3T$, $a[4i+3] = Z[i] + 4T$ and $a[4i] = 20T$ has a solution $a[i'] + a[j'] = a[i' + j']$, $i' + j' < 4N$, if and only if $(X, Y, Z)$ has a solution.

## Sources

- T. M. Chan and Q. He, "Reducing 3SUM to Convolution-3SUM", Symposium on Simplicity in Algorithms (SOSA), 2020.
- V. Vassilevska Williams and R. Williams, "Finding, Minimizing, and Counting Weighted Subgraphs", SIAM Journal on Computing 42(3), 2013.
