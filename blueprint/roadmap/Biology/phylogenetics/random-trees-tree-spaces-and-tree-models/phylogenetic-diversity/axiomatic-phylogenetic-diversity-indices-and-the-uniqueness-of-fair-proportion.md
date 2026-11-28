# Axiomatic phylogenetic diversity indices and the uniqueness of Fair Proportion

Let $T = (V, E)$ be a rooted phylogenetic $X$-tree with positive edge lengths $\ell$, and let $c_T(e)$ be the set of leaves descended from edge $e$. Phylogenetic diversity is $\mathrm{PD}(T) = \sum_{e \in E}\ell(e)$. An **allocation function** is $\varphi_\ell(x) = \sum_{e \in E}\gamma(x, e)\,\ell(e)$ with coefficients $\gamma(x,e) \ge 0$ independent of $\ell$ and $\sum_{x \in X}\varphi_\ell(x) = \mathrm{PD}(T)$ for every $\ell$; equivalently $\sum_x \gamma(x, e) = 1$ for every edge. A **diversity index** is an allocation function that also satisfies

- (DI1, descent) $\gamma(x, e) = 0$ unless $x \in c_T(e)$;
- (DI2, neutrality) the coefficients of $e$ depend only on the tree shape of the pendant subtree below $e$, and leaves in corresponding positions of pendant subtrees of the same shape receive equal coefficients.

The **Fair Proportion** index has $\gamma(x,e) = 1/|c_T(e)|$ for $x \in c_T(e)$; the **Equal-Splits** index divides each edge's length equally at every branching on the way down to $x$.

**Theorem.**
1. For every diversity index, $\gamma(x,e) \le 1$, $\sum_{x \in c_T(e)}\gamma(x,e) = 1$, and the length of a pendant edge goes entirely to its leaf.
2. (Convexity) For fixed $T$ and $\ell$, the set $S(T,\ell) \subset \mathbb R^{|X|}$ of index score vectors $(\varphi_\ell(x))_{x \in X}$ of all diversity indices is convex and compact, and its dimension depends only on the shape of $T$; Fair Proportion and Equal-Splits are two points of this space.
3. (Continuity characterizes Fair Proportion) A diversity index $\psi$ satisfies $\lim_{\ell(e) \to 0}\psi_T(x) = \psi_{T/e}(x)$ for every tree $T$, every leaf $x$ and every interior edge $e$ (where $T/e$ contracts $e$) if and only if $\psi$ is the Fair Proportion index.

## Expansion

Part 1 combines the edge-wise sum-to-one condition with descent; for a pendant edge the only descendant leaf receives everything. Part 2: a convex combination of two coefficient matrices is non-negative, has column sums $1$, and preserves the zero pattern of (DI1) and the equalities of (DI2), so it is again a diversity index; score vectors are linear in the coefficients. Compactness follows from bounds on each leaf's score, between its pendant edge length and its root path length. For part 3, if $e_i$ has only pendant edges below it, neutrality forces equal shares $1/n_i$ among its $n_i$ descendant leaves. If interior edges lie below $e_i$, contracting them one by one leaves the coefficients of $e_i$ unchanged by continuity but produces a tree in which $e_i$ has only pendant edges below it, so again $\gamma(x, e_i) = 1/n_i$; this is Fair Proportion. Conversely Fair Proportion's coefficients depend only on cluster sizes, which contraction of another edge does not change. Fair Proportion is thus the index that is robust to later resolution of polytomies; it also equals the Shapley value of the PD game.

## Sources

- K. Manson, M. Steel, "Spaces of phylogenetic diversity indices: combinatorial and geometric properties", Bulletin of Mathematical Biology 85 (2023) 78, Definitions 1–4, Lemma 2, Propositions 3, 5 and 7, and Theorem 6, <https://doi.org/10.1007/s11538-023-01183-y>, PMCID PMC10328879.
