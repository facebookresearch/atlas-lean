# Knuth's exact mean successful-search cost for linear probing

Let $1 \le k \le N$. In a cyclic table of $N$ cells holding $k$ items inserted by linear probing
with independent uniform hash addresses, the [average cost of a successful search](successful-search-cost.md) is

$$T(N, k) = \frac{1}{2}\bigl(1 + E_0(N, k)\bigr), \qquad
E_0(N, k) = \sum_{j=0}^{k-1} \frac{(k-1)(k-2)\cdots(k-j)}{N^j}.$$

Knuth's 1963 note derives this in Section 7 by averaging the second form of Theorem 2,
$M(N, t) = \frac12\bigl(1 + t E_0(N, t) - (t - 1)E_0(N, t - 1)\bigr)$, which telescopes.

## Informally uses

- [Knuth's exact mean insertion cost for linear probing](insertion-cost-eq.md): the identity
  that is averaged.

## Sources

- D. E. Knuth, "Notes on 'open' addressing", 22 July 1963, typeset by H. Prodinger in 1997,
  Sections 5 and 7: https://jeffe.cs.illinois.edu/teaching/datastructures/2011/notes/knuth-OALP.pdf
