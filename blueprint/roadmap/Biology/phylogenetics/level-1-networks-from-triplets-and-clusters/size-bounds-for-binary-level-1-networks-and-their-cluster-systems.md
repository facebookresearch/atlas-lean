# Size bounds for binary level-1 networks and their cluster systems

A **phylogenetic network** on a finite leaf set $X$ is a rooted DAG with leaf set $X$ whose non-root interior vertices are split vertices (in-degree $1$, out-degree $\ge 2$) or hybrid vertices (in-degree $\ge 2$, out-degree $\ge 1$). It is **binary** if the root has out-degree $2$ and every other interior vertex has total degree $3$. A binary network is **level-1** if every biconnected component of its underlying undirected graph contains at most one hybrid vertex; it is assumed that every cycle has at least four vertices. A non-trivial biconnected component is a **gall**; $g(N)$ is the number of galls. An arc is a **cut arc** if deleting it disconnects the underlying graph, and **non-trivial** if its head is not a leaf; $c_N$ is the number of non-trivial cut arcs. Write $\mathcal L_1(n)$ for the binary level-1 networks on $n$ leaves and $\mathcal L_1(n)^-$ for the proper ones (at least one hybrid vertex, $n \ge 3$).

For a vertex $v$ let $C_N(v)$ be the set of leaves below $v$. The **softwired cluster system** $\mathcal S(N)$ is the union of the cluster systems $\{C_T(u)\}$ of all phylogenetic trees $T$ displayed by $N$, and $\mathcal S(N)^- = \mathcal S(N) \setminus \{X\}$.

**Lemma (vertices and arcs).** For $n \ge 3$ and $N = (V,A) \in \mathcal L_1(n)^-$,

$$2n + 1 \le |V| \le 3n - 2, \qquad 2n + 1 \le |A| \le 3.5\,(n-1),$$

with equality throughout when $n = 3$, in which case $N$ is simple.

**Theorem (galls).** For $n \ge 2$ and $N \in \mathcal L_1(n)$, $g(N) \le n - c_N - 2$, with equality if $N$ is a tree or every gall has exactly three outgoing arcs.

**Theorem (cluster count).** For $n \ge 2$ and $N \in \mathcal L_1(n)$,

$$|\mathcal S(N)^-| = 3n - 4 - c_N.$$

**Proposition (no triplet analogue).** For every $n \ge 6$ there are $N_1, N_2 \in \mathcal L_1(n)$ with the same numbers of galls and of non-trivial cut arcs but $|\mathcal R(N_1)| \ne |\mathcal R(N_2)|$, where $\mathcal R(N)$ is the set of rooted triplets displayed by $N$.

## Expansion

For a binary tree ($g = 0$) there are $2n - 1$ vertices and $2(n-1)$ arcs; a simple level-1 network (one gall with every leaf hanging from it) has $|V| = |A| = 2n+1$, and general bounds follow by decomposing a proper network along its non-trivial cut arcs into simple pieces and trees and counting how each gall replaces tree vertices. Each vertex contributes at most two softwired clusters, so $|\mathcal S(N)| = O(n)$; the exact formula follows by induction on restrictions $N|_{X'}$ to leaf subsets, removing a cherry or a leaf on a gall and tracking which clusters disappear. The cluster count therefore depends only on $n$ and $c_N$, but two networks that differ only in which side of a gall a pendant subtree hangs from can induce different numbers of triplets, so no comparable formula exists for $|\mathcal R(N)|$.

## Sources

- P. Gambette, K. T. Huber, S. Kelk, "On the challenge of reconstructing level-1 phylogenetic networks from triplets and clusters", Journal of Mathematical Biology (2017), Sections 2–4, Lemma 3.1, Theorem 3.2, Theorem 4.1 and Proposition 4.2, <https://doi.org/10.1007/s00285-016-1068-3>, PMCID PMC5420025.
