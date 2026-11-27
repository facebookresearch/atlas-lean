# Convolution-3SUM

**Convolution-3SUM** (three-array form). Given integer arrays $X, Y, Z$ indexed by $\{0, \dots, N-1\}$, decide whether there are indices $i, j$ with $i + j < N$ and

$$
X[i] + Y[j] = Z[i + j].
$$

This is the version of Chan and He (Definition 2.2). The one-array version asks for $i, j$ with $a[i] + a[j] = a[i+j]$; Chan and He (Appendix A) remark that the one-array and three-array versions are equivalent.

## Proof sketch

Three arrays reduce to one: with $B = \max_i \max(|X[i]|, |Y[i]|, |Z[i]|)$ and $T = 3B + 1$, let $a$ have length $4N$ with $a[4i+1] = X[i] + T$, $a[4i+2] = Y[i] + 3T$, $a[4i+3] = Z[i] + 4T$ and $a[4i] = 20T$. Comparing residues modulo $4$ and the value ranges $T \pm B$, $3T \pm B$, $4T \pm B$ and $20T$ shows that the only possible solutions $a[i'] + a[j'] = a[i' + j']$ with $i' + j' < 4N$ are $X[i] + T + Y[j] + 3T = Z[i+j] + 4T$ with $i + j < N$, up to the order of $i'$ and $j'$; so $a$ has a solution if and only if $(X, Y, Z)$ has one.

## Sources

- T. M. Chan and Q. He, "Reducing 3SUM to Convolution-3SUM", Symposium on Simplicity in Algorithms (SOSA), 2020.
- V. Vassilevska Williams and R. Williams, "Finding, Minimizing, and Counting Weighted Subgraphs", SIAM Journal on Computing 42(3), 2013.
