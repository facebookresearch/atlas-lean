# The height lemma for LCP arrays

Let $\mathrm{sa}$ be the suffix array of $w$, $\mathrm{rk}$ its inverse, and $h(i)$ the length of the longest common prefix of the suffix starting at $i$ with its predecessor in suffix-array order (when it has one). Then for every $i$ with $\mathrm{rk}(i) > 0$ and $\mathrm{rk}(i+1) > 0$,

$$
h(i + 1) \ge h(i) - 1 .
$$

## Proof sketch

If $j$ precedes $i$ in suffix order and they share a prefix of length $h(i) \ge 1$, then $j + 1$ precedes $i + 1$ and shares a prefix of length $h(i) - 1$; the immediate predecessor of $i+1$ shares at least as much.

## Depends on

- [Suffix array](../../data-structures/tries-and-integer-dictionaries/suffix-array/suffix-array.md)
- [The LCP array](../../data-structures/tries-and-integer-dictionaries/suffix-array/lcp-array.md)

## Sources

- T. Kasai, G. Lee, H. Arimura, S. Arikawa and K. Park, "Linear-Time Longest-Common-Prefix Computation in Suffix Arrays and Its Applications", Combinatorial Pattern Matching (CPM 2001), LNCS 2089, Springer, 2001.
