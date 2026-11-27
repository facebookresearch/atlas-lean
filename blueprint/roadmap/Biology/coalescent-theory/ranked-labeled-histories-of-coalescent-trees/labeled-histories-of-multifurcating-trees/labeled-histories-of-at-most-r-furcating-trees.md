# Labeled histories of at-most-r-furcating trees

**Setting.** A rooted leaf-labeled tree is *at-most-$r$-furcating* if every internal node has between $2$ and $r$ children. A *labeled history* of a labeled topology $T$ is a linear ordering of its internal nodes compatible with ancestry, that is, a linear extension of the poset of internal nodes ordered by descent (without simultaneity); with simultaneity allowed, several internal nodes may share a time rank.

**Theorem.**
1. Without simultaneous events, the total number $A_r(n)$ of labeled histories over all at-most-$r$-furcating labeled topologies on $n$ leaves satisfies $A_r(1) = 1$ and

$$A_r(n) = \sum_{i=2}^{\min\{n, r\}} \binom{n}{i} A_r(n + 1 - i), \qquad n \ge 2 .$$

2. Without simultaneous events, a fixed labeled topology $T$ with $n \ge 2$ leaves has

$$N(T) = \frac{w(T)!}{\prod_{v \in V^0(T)} w(v)}$$

labeled histories, where $V^0(T)$ is the set of internal nodes and $w(v)$ is the number of internal nodes in the subtree rooted at $v$ (including $v$).
3. With simultaneous events, the total number $S_r(n)$ satisfies $S_r(1) = 1$ and, for $n \ge 2$,

$$S_r(n) = \sum_{\substack{(x_2, \dots, x_r):\ 2 \le \sum_j j x_j \le n}} \frac{n!}{\bigl[\prod_{j=2}^r (j!)^{x_j} x_j!\bigr]\,\bigl(n - \sum_j j x_j\bigr)!}\; S_r\Bigl(n - \sum_{j=2}^r (j-1) x_j\Bigr),$$

where $x_j$ is the number of simultaneous $j$-mergers in the most recent event.

## Depends on

- [Linear extensions of a finite poset](../../../../Combinatorics/partially-ordered-sets/linear-extensions-of-posets/linear-extensions.md)

## Related topics

- [Number of ranked labeled histories](../card-ranked-history.md): the bifurcating case $r = 2$ of item 1.

## Proof idea

Reading a history backwards from the leaves, the most recent event merges $i$ of the $n$ current lineages into one, leaving $n + 1 - i$ lineages; summing over $i \le r$ gives the recursion for $A_r$, which for $r = 2$ reduces to $A_2(n) = n!(n-1)!/2^{n-1}$. For a fixed topology, a labeled history is a linear extension of the internal-node poset, a rooted forest, and the hook-length formula for forests gives $N(T)$, independent of the furcation degrees. With simultaneity, the most recent event is a set of disjoint mergers whose multiset of sizes is counted by the multinomial coefficient.

## Sources

- E. H. Dickey and N. A. Rosenberg, "Labeled histories and maximally probable labeled topologies with multifurcation", Discrete Applied Mathematics 391 (2026), 192–203, <https://doi.org/10.1016/j.dam.2026.04.032>. Numbering as in the preprint arXiv:2511.16799v1, <https://arxiv.org/abs/2511.16799v1>: Propositions 1, 2 and 10.
