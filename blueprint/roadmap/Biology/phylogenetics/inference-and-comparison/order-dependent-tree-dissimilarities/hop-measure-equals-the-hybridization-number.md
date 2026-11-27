# HOP measure equals the hybridization number

**Trees and orderings.** Let $X$ be a finite set with $|X| = n$. A rooted binary phylogenetic $X$-tree has a root $\rho$ of out-degree one, leaves bijectively labeled by $X$ and all other vertices of in-degree one and out-degree two. An **ordering** is a bijection $\sigma : X \to \{1, \dots, n\}$.

**HOP vector.** Label each leaf $x$ by $\underline{\sigma(x)}$. For a vertex $v$ let $m(v)$ be the smallest leaf label below $v$; label each internal non-root vertex $v$ with children $v_1, v_2$ by $\max\{m(v_1), m(v_2)\}$, and label $\rho$ by $1$. This puts the non-leaf vertices in bijection with $\{1, \dots, n\}$. For $i = 1, \dots, n$ let $P_i$ be the path from the non-leaf vertex labeled $i$ to the leaf labeled $\underline i$, and let $\mathbf v_i$ be the sequence of labels of the interior vertices of $P_i$. The HOP vector is $[1, \mathbf v_1, \underline 1, \mathbf v_2, \underline 2, \dots, \mathbf v_{n-1}, \underline{n-1}, \underline n]$. For two trees $T, T'$ with HOP blocks $\mathbf u_i, \mathbf v_i$ under $\sigma$,

$$d^\sigma_{\mathrm{HOP}}(T, T') = (n-1) - \sum_{i=1}^{n-1} \big|\mathrm{LCS}(\mathbf u_i, \mathbf v_i)\big|,$$

where LCS is a longest common subsequence. Each internal non-root vertex $u$ is an interior vertex of exactly one path, $P_{m(u)}$, so the blocks of a tree hold $n-1$ labels in all and $d^\sigma_{\mathrm{HOP}}(T, T')$ is the number of block labels outside a longest common subsequence; in particular $d^\sigma_{\mathrm{HOP}}(T, T) = 0$. For fixed $\sigma$ this is a metric on $X$-trees. The **HOP measure** is $d^*_{\mathrm{HOP}}(T, T') = \min_\sigma d^\sigma_{\mathrm{HOP}}(T, T')$; it is not a metric (it can violate the triangle inequality).

**Hybridization number.** $h(T, T')$ is the minimum number of in-degree-two vertices of a rooted binary phylogenetic network on $X$ displaying both $T$ and $T'$; it equals $m_a(T, T')$, the minimum number of components minus one of an acyclic agreement forest for $T$ and $T'$.

**Statement.** For all rooted binary phylogenetic $X$-trees $T, T'$,

$$d^*_{\mathrm{HOP}}(T, T') = h(T, T').$$

Moreover $d^*_{\mathrm{OLA}}(T, T') \le h(T, T')$ and $d^*_{\mathrm{P2V}}(T, T') \le h(T, T')$ for the ordered-leaf-attachment and Phylo2Vec measures. Since computing $h$ is NP-hard, computing $d^*_{\mathrm{HOP}}$ is NP-hard.

## Expansion

Upper bound: take a maximum acyclic agreement forest and order $X$ so that the components appear in an order compatible with its acyclic inheritance graph, with the leaves of each component consecutive. A common pendant subtree receives identical HOP labels in both trees (and identical OLA vector entries), so each block $\mathbf u_i, \mathbf v_i$ loses common-subsequence length only where a component is cut off, giving at most $m_a(T, T')$ mismatches. Lower bound: from an ordering attaining $d^*_{\mathrm{HOP}}$, the paths whose blocks fail to share a full common subsequence define cuts of $T$ and $T'$ whose pieces form an acyclic agreement forest with at most $d^*_{\mathrm{HOP}}$ cut edges, so $d^*_{\mathrm{HOP}} \ge m_a = h$.

## Depends on

- [OLA measure is bounded by the rSPR distance](ola-measure-is-bounded-by-the-rspr-distance.md)

## Sources

- S. Linz, K. St. John, C. Semple and K. Wicke, "Order-dependent dissimilarity measures on phylogenetic trees", *Journal of Mathematical Biology* 92(4) (2026), 53, Theorem 2, Theorem 4, Theorem 5, Lemma 7, Corollary 1, <https://doi.org/10.1007/s00285-026-02373-7> (preprint arXiv:2507.11254).
