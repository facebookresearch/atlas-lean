# Colless index and its root decomposition

Let $T$ be a rooted bifurcating tree with leaf set of size $n \ge 1$, let $\mathring V(T)$ be its set of internal nodes and, for a node $v$, let $\kappa_T(v)$ be the number of leaves descending from $v$. The **balance value** of an internal node $v$ with children $v_1, v_2$ is $\mathrm{bal}_T(v) = |\kappa_T(v_1) - \kappa_T(v_2)|$.

**Definition (Colless index).**

$$C(T) = \sum_{v \in \mathring V(T)} \mathrm{bal}_T(v) = \sum_{v \in \mathring V(T)} |\kappa_T(v_1) - \kappa_T(v_2)|.$$

It depends only on the shape of $T$, not on the leaf labels.

**Root decomposition.** If $n \ge 2$ and $T = (T_a, T_b)$ is the decomposition of $T$ into its two maximal pending subtrees, with $n_a \ge n_b$ leaves, then

$$C(T) = C(T_a) + C(T_b) + n_a - n_b.$$

**Zero index.** For every $n \ge 1$ and every bifurcating tree $T$ with $n$ leaves, $C(T) = 0$ if and only if $n$ is a power of $2$ and $T$ is the fully symmetric tree (every internal node has two children with equal numbers of descendant leaves).

## Expansion

The decomposition is immediate: the internal nodes of $T$ are the root, whose balance value is $n_a - n_b$, and the internal nodes of $T_a$ and $T_b$, whose descendant-leaf counts are unchanged. The zero-index statement follows by induction on $n$: $C(T) = 0$ forces $n_a = n_b$ and $C(T_a) = C(T_b) = 0$. The maximum value $(n-1)(n-2)/2$ is attained by the caterpillar.

## Sources

- T. M. Coronado, M. Fischer, L. Herbst, F. Rosselló and K. Wicke, "On the minimum value of the Colless index and the bifurcating trees that achieve it", *Journal of Mathematical Biology* (2020), <https://doi.org/10.1007/s00285-020-01488-9> (Definition 3, Lemma 1 and Corollary 1; numbering as in the arXiv version 1907.05064v2).
