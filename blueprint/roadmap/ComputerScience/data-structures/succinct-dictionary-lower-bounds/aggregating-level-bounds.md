# Aggregating level bounds over the meta-operation tree

Fix $t, \gamma > 0$ and a meta-operation tree over the $n$ meta-operations of a hard dictionary distribution, and let $L$ be a set of levels such that every node $u$ at every level $\ell \in L$ satisfies $\mathbb{E}[\mathrm{cost}_u] \ge \frac{\gamma}{100} m_\ell$ or $\mathbb{E}[\mathrm{probe}_u] \ge \frac{1}{16} m_\ell t$. Then the expected total number of probes is at least

$$
\min\left(\frac{n t}{32},\; \frac{\gamma}{200}\, n\, |L|\right).
$$

The source supplies two schedules for which the outer lemma gives such a set $L$ for all sufficiently large $n$, with $t = \gamma \log_2 U / (8(\beta+1))$:

1. for redundancy $R \le n \log^{(k)} n$ with $1 \le k \le \log^* n$: $m_\ell = c\, n \log^{(k)} n / \log^{(\ell)} n$ with $c = 10^6$ up to the root level $h = \min\{\ell : \log^{(\ell)} n \le c \log^{(k)} n\}$, and $L = \{2, \dots, h-1\}$, where $h = \Omega(k)$;
2. for redundancy $R \le n$: $m_1 = \max(R, n^{1-\gamma/2})$, constant fanout $2^{64}$ above level 1, root level $h = \log_{2^{64}}(n/m_1) = \Omega(\log(n/R))$, and $L = \{2, \dots, h\}$.

## Proof sketch

If at some level of $L$ at least half of the $n/m_\ell$ nodes satisfy the second alternative, then, since the $\mathrm{probe}_u$ of one level sum to the total probe count, the expected total is at least $\frac{1}{2} \cdot \frac{n}{m_\ell} \cdot \frac{m_\ell t}{16} = \frac{nt}{32}$. Otherwise every level of $L$ has at least half of its nodes satisfying the first alternative, and since assigned probes are disjoint, the expected total is at least $\sum_{\ell \in L} \frac{1}{2} \cdot \frac{n}{m_\ell} \cdot \frac{\gamma}{100} m_\ell = \frac{\gamma}{200} n |L|$. The schedules are checked against the four premises of the outer lemma level by level.

## Depends on

- [Meta-operation tree and probe attribution](meta-operation-tree.md)
- [Outer lemma: each tree node forces many attributed probes or many probes](outer-lemma.md)
- [Iterated logarithm and log-star](../hashing/succinct-dictionaries-and-hash-families/dictionary-specifications/iterated-logarithm.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Tight Cell-Probe Lower Bounds for Dynamic Succinct Dictionaries", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science (FOCS), pp. 1842-1862, 2023; arXiv:2306.02253.
