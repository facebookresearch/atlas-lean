# Law of the lineages leaving a species-tree branch

For a [species tree](species-tree.md) $T$ and a real function $k$ of a number of lineages, a list of lineages and a set of clusters, the exit law $X_T(k)$ is defined recursively:

- for a leaf $\ell(i)$, $X_{\ell(i)}(k) = k\bigl(1, (\{i\}), \{\{i\}\}\bigr)$;
- for a node $(l, r, t)$, $X_{(l,r,t)}(k)$ is $X_l$ applied to the function $(m_l, b_l, A_l) \mapsto X_r\bigl((m_r, b_r, A_r) \mapsto B\bigr)$, where $B$ is the [branch step](branch-step.md) along a branch of length $t$ that receives the $m_l + m_r$ lineages $b_l$ followed by $b_r$ and the clusters $A_l \cup A_r$, with continuation $k$.

When all branch lengths of $T$ are nonnegative, $X_T(k)$ is the expectation of $k(m, b, A)$, where $m$ is the number of lineages leaving the top of the branch above the root of $T$, $b$ the list of these lineages and $A$ the clusters formed below; the two daughter populations evolve independently and their lineages enter the ancestral population together.
