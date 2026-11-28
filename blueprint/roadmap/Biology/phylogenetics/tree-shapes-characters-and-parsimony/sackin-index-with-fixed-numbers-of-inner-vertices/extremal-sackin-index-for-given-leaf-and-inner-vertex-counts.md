# Minimal and maximal Sackin index for given numbers of leaves and inner vertices

**Setting.** Let $T$ be a rooted tree (no vertex of out-degree $1$) with $n$ leaves and $m$ inner vertices; necessarily $m\le n-1$, with $m=n-1$ exactly for binary trees, and $(n,m)=(1,0)$ for the one-vertex tree. The depth $\delta_T(v)$ is the number of edges from the root $\rho$ to $v$, $n_v$ is the number of leaves below $v$, and the **Sackin index** is

$$S(T)=\sum_{x\in V_L(T)}\delta_T(x)=\sum_{v\in\mathring V(T)} n_v .$$

Write $T^{star}_k$ for the star tree with $k$ leaves and $T^{fb}_h$ for the fully balanced binary tree of height $h$.

**Theorem (maximum).** For $n\ge2$ and $1\le m\le n-1$ there is exactly one tree with $n$ leaves, $m$ inner vertices and maximal Sackin index: the caterpillar on $m+1$ leaves with $n-m-1$ further leaves attached to its deepest inner vertex. Consequently every such $T$ satisfies

$$S(T)\le nm-\frac{(m-1)m}{2}\le \frac{n(n+1)}{2}-1=S(T^{cat}_n),$$

and the first bound is attained for every admissible $(n,m)$.

**Theorem (minimum).** Let $k=n-m+1$ and $(n,m)\ne(1,0)$. The following are equivalent:

1. $T$ has minimal Sackin index among trees with $n$ leaves and $m$ inner vertices;
2. $T$ is obtained by taking $T^{star}_k$, replacing each of its leaves by $T^{fb}_{\delta-1}$ with $\delta=\lfloor\log_2(n/k)\rfloor+1$, and then replacing $n-k\,2^{\delta-1}$ of the resulting leaves by cherries;
3. $S(T)=\left\lfloor\log_2\frac{n}{k}\right\rfloor n+3n-k\,2^{\lfloor\log_2(n/k)\rfloor+1}$.

Equivalently, the minimizers are exactly the trees whose root has $k$ children, all of whose non-root inner vertices are binary, and whose leaf depths differ pairwise by at most $1$. Unlike the maximizer, the minimizer need not be unique; the number $s(n,m)$ of minimizers satisfies

$$s(n,m)=\sum_{\{(a_1,\tilde n_1),\dots,(a_l,\tilde n_l)\}\in\mathcal P_k(n)}\ \prod_{i=1}^{l}\binom{s(\tilde n_i,\tilde n_i-1)+a_i-1}{a_i},$$

where $\mathcal P_k(n)$ is the set of partitions $n=\sum_i a_i\tilde n_i$ into $k=\sum_i a_i$ parts with $2^{\delta-1}\le\tilde n_i\le2^{\delta}$, and $s(n',n'-1)$ counts Sackin-minimal binary trees. Dividing by $n$ gives the same statements for the average leaf depth $\overline N(T)=S(T)/n$.

## Expansion

*Maximum.* If a tree is not a caterpillar decorated at its deepest inner vertex, it has two "generalized cherries"; detaching the shallower one, re-hanging its children below the deeper one and inserting a new parent keeps $n$ and $m$ fixed while no leaf gets shallower and some get strictly deeper, so $S$ increases. Summing $n_{v_i}=n-i+1$ along the spine of the extremal tree gives $nm-(m-1)m/2$, which is increasing in $m$ and equals $S(T^{cat}_n)$ at $m=n-1$.

*Minimum.* In a minimizer, an unresolved non-root vertex can push all but two children up to the root, strictly lowering $S$; and two leaves whose depths differ by at least $2$ allow swapping a deepest cherry with the shallow leaf, lowering $S$ by at least $1$. Hence all non-root inner vertices are binary, so the root has $k=n-m+1$ binary pending subtrees, and all leaf depths lie in $\{\delta,\delta+1\}$; counting leaves forces $\delta=\lfloor\log_2(n/k)\rfloor+1$. Starting from $k\,2^{\delta-1}$ leaves at depth $\delta$ and adding $n-k2^{\delta-1}$ cherries, each raising $S$ by $\delta+2$, yields the closed form. For $m=n-1$ ($k=2$) this recovers the binary characterization of Sackin-minimal trees; e.g. $n=4$ gives $S=8=S(T^{fb}_2)$.

## Depends on

- [Balance and imbalance index axioms for rooted tree shapes](../axioms-of-tree-balance-indices/balance-and-imbalance-index-axioms.md)

## Sources

- Mareike Fischer, Lina Herbst, Sophie Kersting, Luise Kühn and Kristina Wicke, "Tree Balance Indices: A Comprehensive Survey", Springer (2023), <https://doi.org/10.1007/978-3-031-39800-1>; numbering as in arXiv:2109.12281: appendix on the average leaf depth and Sackin index: Theorem 1, Proposition 7, Corollary 1 (maximum), Lemma 1, Theorem 2, Corollaries 2–3 (minimum).
- M. Fischer, "Extremal values of the Sackin tree balance index", Annals of Combinatorics (2021), Theorem 2 (binary case).
