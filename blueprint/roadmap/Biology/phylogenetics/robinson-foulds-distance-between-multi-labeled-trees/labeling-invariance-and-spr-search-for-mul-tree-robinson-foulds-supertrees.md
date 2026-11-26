# Labeling invariance and SPR search for mul-tree Robinson–Foulds supertrees

**Setting.** Let $\mathcal P = (\mathcal T_1, \dots, \mathcal T_k)$ be a profile of mul-trees (multi-copy gene trees) and $\mathcal S = (S, \phi)$ a singly labeled binary species tree whose label set contains those of the $\mathcal T_i$. The *extension* $\mathcal S^*$ of $\mathcal S$ relative to a mul-tree $\mathcal T = (T, \varphi)$ replaces every leaf $s$ whose label appears $c > 1$ times in $\mathcal T$ by an internal vertex joined to $c$ leaves labeled $\phi(s)$. Define $\mathrm{RF}(\mathcal T, \mathcal S) = \mathrm{RF}(\mathcal T, \mathcal S^*)$, using the [mul-tree Robinson–Foulds distance](np-completeness-of-the-robinson-foulds-distance-between-mul-trees.md), and $\mathrm{RF}(\mathcal P, \mathcal S) = \sum_{\mathcal T \in \mathcal P} \mathrm{RF}(\mathcal T, \mathcal S)$. The MulRF problem asks for a binary species tree minimizing $\mathrm{RF}(\mathcal P, \mathcal S)$; it is NP-hard even for singly labeled inputs on a common leaf set.

**Theorem (labeling invariance).** For a mul-tree $\mathcal T$ and the extension $\mathcal S^*$ of a species tree, every pair of consistent full differentiations $(T_1, S_1)$ and $(T_2, S_2)$ of $\mathcal T$ and $\mathcal S^*$ satisfies $\mathrm{RF}(T_1, S_1) = \mathrm{RF}(T_2, S_2)$. Hence $\mathrm{RF}(\mathcal P, \mathcal S)$ is computed in polynomial time by differentiating copies arbitrarily (for instance $a \mapsto a_1, \dots, a_c$ in both trees).

**Theorem (SPR search).** Let $n = |S|$, $m = |T| + |S|$ for each input tree (all of similar size), and $k = |\mathcal P|$. A species tree minimizing $\mathrm{RF}(\mathcal P, \cdot)$ over the SPR neighborhood of $\mathcal S$ can be found in $\Theta(nmk)$ time.

## Depends on

- [NP-completeness of the Robinson–Foulds distance between mul-trees](np-completeness-of-the-robinson-foulds-distance-between-mul-trees.md)

## Expansion

Invariance: in $\mathcal S^*$ all copies of a label form a cherry-like star under one vertex, so splits of the differentiated gene tree either keep all copies of $a$ on one side (and are matched independently of the labeling) or separate them (and can never be matched); permuting new labels therefore leaves the matched count unchanged. For the search, with $T$ the differentiated gene tree, $\mathrm{RF}(T, S) = |\mathcal L(T)| - |I(T)| + 2|F_S| - 2$, where $F_S$ is the set of internal vertices of $T$ whose vertex function (computed from LCA mappings) is zero. Pruning one side of an edge $\{x, y\}$ of $S$ and regrafting it along all edges of the other side changes $F_S$ by local gains and losses, so after one $\Theta(m)$ initialization each regraft is scored in constant time; $\Theta(n)$ edges and $k$ gene trees give $\Theta(nmk)$.

## Sources

- R. Chaudhary, J. G. Burleigh and D. Fernández-Baca, "Inferring species trees from incongruent multi-copy gene trees using the Robinson-Foulds distance", *Algorithms for Molecular Biology* 8 (2013) 28, Problem 1 (MulRF), Theorem 3, Lemmas 2 and 4–5, Problem 2 and Theorem 4. <https://doi.org/10.1186/1748-7188-8-28> (PMC3874668)
