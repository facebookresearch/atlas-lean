# Fenwick prefix queries and updates have logarithmically many probes

A [Fenwick tree](fenwick-tree.md) for an array of length $n$ stores a block at each one-indexed endpoint $1 \le j \le n$. Write $\operatorname{lowbit}(j)$ for the largest power of two dividing $j$. The block consists of the zero-indexed array positions in $[j-\operatorname{lowbit}(j),j)$. The prefix walk starts at $\min(k,n)$ for a requested length $k$ and repeatedly subtracts the current endpoint's low bit, stopping before $0$. The point-update walk starts at the one-indexed position $i$ and repeatedly adds the current endpoint's low bit, visiting only endpoints in $[1,n]$.

**Theorem.** For natural numbers $n,k,i$:

1. Concatenating the prefix walk's blocks in reverse visit order gives the consecutive list of positions $0,\ldots,\min(k,n)-1$, without omissions or repetitions. The walk is empty for $n=0$ or $k=0$, and uses the full prefix for $k>n$.
2. The update walk is strictly increasing. It visits exactly the endpoints $j\le n$ with $j-\operatorname{lowbit}(j)<i\le j$, so each visited block contains the updated position and no entry is visited twice. The walk is empty for $i=0$ or $i>n$.
3. For $n>0$, each walk visits at most $\lfloor\log_2 n\rfloor+1$ entries. The same inequalities hold for $n=0$ with the convention $\operatorname{log2}(0)=0$.

The [prefix query](prefix-sum-eq-sum-prefix-visits.md) reads the stored entries of the prefix
walk. An [update](get-d-add-eq.md) at zero-indexed array position $p$ reads and writes once per
visit of the update walk starting at $i=p+1$. These correspondences do not assume that the
storage represents an underlying array.

After dividing a positive endpoint by its low bit, the quotient is odd. Adding or subtracting that low bit therefore makes the next endpoint a multiple of twice the previous low bit. At any nonzero next visit the exponent increases, and no visited endpoint exceeds $n$. This counts index visits, not the cost of arithmetic or of copying a persistent array.

In zero-based stored indices $r=j-1$, subtracting or adding the low bit corresponds to the respective jumps $g(r)-1$ and $h(r)$, where $g(r)=r\mathbin{\&}(r+1)$ and $h(r)=r\mathbin{|}(r+1)$. The stopping index $-1$ for the zero-based prefix walk corresponds to the unvisited endpoint $0$.

## Background

- [Fenwick tree prefix sum](prefix-sum.md)
- [Point update of a Fenwick tree](add.md)

## Sources

- cp-algorithms, [Fenwick Tree](https://cp-algorithms.com/data_structures/fenwick.html), the zero-based prefix and point-update walks and the one-based indexing approach.
