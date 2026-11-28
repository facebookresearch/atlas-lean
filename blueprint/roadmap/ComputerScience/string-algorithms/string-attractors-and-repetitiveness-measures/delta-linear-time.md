# Substring complexity is computable in linear time

For a string $T[1..n]$ over an integer alphabet, all values $d_1(T), \dots, d_n(T)$, and hence $\delta(T)$, can be computed in $O(n)$ time.

## Proof sketch

The distinct substrings of length $k$ correspond to the suffixes of length at least $k$, counted once per maximal group sharing a common prefix of length $k$. In suffix-array order with the LCP array, a suffix of length at least $k$ starts a new length-$k$ substring exactly when its LCP with the previous suffix is less than $k$; hence $d_k = |\{ j : |\text{suffix}_j| \ge k > \mathrm{LCP}[j] \}|$, and all $d_k$ follow from prefix sums over a difference array indexed by the intervals $(\mathrm{LCP}[j], |\text{suffix}_j|]$. Suffix and LCP arrays are built in linear time.

## Depends on

- [Substring complexity $\delta$](substring-complexity.md)

## Proof depends on

- [Suffix array](../../data-structures/tries-and-integer-dictionaries/suffix-array/suffix-array.md)
- [The LCP array](../../data-structures/tries-and-integer-dictionaries/suffix-array/lcp-array.md)
- [Kasai's algorithm runs in linear time](../../data-structures/tries-and-integer-dictionaries/suffix-array/construction-time-of-suffix-arrays-lcp-arrays-and-suffix-trees.md)

## Sources

- Tomasz Kociumaka, Gonzalo Navarro, Nicola Prezza, "Toward a Definitive Compressibility Measure for Repetitive Sequences", IEEE Transactions on Information Theory 69(4) (2023); LATIN (2020), arXiv:1910.02151.
- Anders Roy Christiansen, Mikko Berggren Ettienne, Tomasz Kociumaka, Gonzalo Navarro, Nicola Prezza, "Optimal-Time Dictionary-Compressed Indexes", ACM Transactions on Algorithms 17(1) (2021), arXiv:1811.12779.
- Toru Kasai, Gunho Lee, Hiroki Arimura, Setsuo Arikawa, Kunsoo Park, "Linear-Time Longest-Common-Prefix Computation in Suffix Arrays and Its Applications", CPM (2001).
