# B2 index of a phylogenetic network and its grafting property

**Definition.** Let $G$ be a finite rooted phylogenetic network (a rooted directed acyclic graph whose sinks are the leaves $\mathcal{L}(G)$). The *directed random walk* on $G$ starts at the root and at each step moves to a uniformly chosen child of its current vertex until it reaches a leaf. Writing $p_\ell$ for the probability that it ends at leaf $\ell$, the $B_2$ index of $G$ is the Shannon entropy (in bits) of this exit distribution,

$$B_2(G) = -\sum_{\ell \in \mathcal{L}(G)} p_\ell \log_2 p_\ell .$$

For a tree it equals $B_2(\mathbf{t}) = \sum_{v \text{ internal}} p_v \log_2 d^+(v)$, the sum over the internal (non-leaf) vertices $v$, where $d^+(v) \ge 1$ is the out-degree of $v$ and $p_v = \prod_u d^+(u)^{-1}$ over the vertices $u$ strictly above $v$ on its root path; leaves contribute no branching entropy.

**Proposition (grafting property).** Let $G_1, G_2$ be finite phylogenetic networks and let $G$ be obtained by identifying a leaf $\ell$ of $G_1$ with the root of $G_2$. Then

$$B_2(G) = B_2(G_1) + p_\ell\, B_2(G_2),$$

where $p_\ell$ is the probability that the directed random walk on $G_1$ ends in $\ell$.

Consequently, if the root of a binary galled tree $G$ is not in a gall and has subtrees $G_1, G_2$, then $B_2(G) = \tfrac12\big(B_2(G_1) + B_2(G_2)\big) + 1$.

## Expansion

The grafting property is the chain rule for entropy: the exit leaf in $G$ is determined by first running the walk in $G_1$ and then, if it reaches $\ell$, running an independent walk in $G_2$; refining the block $\{\ell\}$ of the exit partition adds $p_\ell$ times the conditional entropy. Larger $B_2$ means more balanced: the maximum $\log_2 n$ on $n$ leaves is attained when the walk is uniform on leaves.

## Sources

- François Bienvenu, Jean-Jil Duchamps, Michael Fuchs and Tsan-Cheng Yu, "The $B_2$ index of galled trees", Advances in Applied Probability (2026), 1–44, <https://doi.org/10.1017/apr.2026.10070>; numbering as in arXiv:2407.19454v2: Definition 1.2 (the $B_2$ index), Proposition 1.3 (grafting property) and Corollary A.26 (tree formula).
