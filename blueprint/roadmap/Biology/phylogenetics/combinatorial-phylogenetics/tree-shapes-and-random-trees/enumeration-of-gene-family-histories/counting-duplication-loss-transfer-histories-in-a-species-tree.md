# Counting duplication–loss–transfer histories of a gene family in a species tree

**Setting.** Let $S$ be a rooted species tree; for a node $u$ let $\overline{C}(u)$ be the set of nodes incomparable with $u$ (neither ancestor nor descendant). An **evolutionary history** of a gene family within $S$ is an ordered rooted unary–binary tree $T$ with maps $s : V(T) \to V(S)$ (species of each gene) and $e : V(T) \to \{\mathrm{Spec}, \mathrm{Dup}, \mathrm{Loss}, \mathrm{Trans}, \mathrm{Extant}\}$ such that leaves are Extant or Loss, binary nodes are Spec, Dup or Trans, unary nodes are Spec, a speciation at a binary $u$ sends the two children to the two children of $u$, a duplication keeps both children in $s(x)$, and a transfer keeps one child in $s(x)$ and sends the other to a node of $\overline{C}(s(x))$. The **size** of a history is its number of Extant leaves. The DL-model forbids transfers; the DLT-model allows them. In a **ranked** species tree the internal nodes are totally ordered in time, and transfers are allowed only between branches coexisting in a time slice.

**Theorem (grammar).** The DLT-histories rooted at node $u$ form the combinatorial class $\mathcal{H}_u$ specified by

$$\mathcal{H}_u = \mathcal{S}_u \cup \mathcal{D}_u \cup \mathcal{T}_u \ (u \text{ internal}), \qquad \mathcal{H}_u = \mathcal{Z}_u \cup \mathcal{D}_u \cup \mathcal{T}_u \ (u \text{ a leaf}),$$

$$\mathcal{S}_u = \mathcal{H}_{u_\ell}\times\mathcal{H}_{u_r} \cup \mathcal{H}_{u_\ell}\times\mathcal{X}_{u_r} \cup \mathcal{X}_{u_\ell}\times\mathcal{H}_{u_r}, \qquad \mathcal{D}_u = \mathcal{H}_u\times\mathcal{H}_u\times\mathcal{Y}_u, \qquad \mathcal{T}_u = \bigcup_{v\in\overline{C}(u)} \mathcal{H}_u\times\mathcal{H}_v\times\mathcal{W}_u,$$

where $\mathcal{Z}_u$ is an extant gene, $\mathcal{X}$ marks a loss and $\mathcal{Y}, \mathcal{W}$ mark the duplication and transfer nodes (with $\mathcal{S}_u = \mathcal{H}_{u_c}$ at unary nodes of a ranked tree). DL-histories are given by the same grammar without $\mathcal{T}_u$.

**Theorem (counting, sampling, asymptotics).**

1. The number of histories of size $n$ in a species tree of size $k$ can be computed in time and space polynomial in $n$ and $k$ (for the DL and DLT models, ranked or unranked), and $h$ uniformly random histories of size $n$ can be sampled after that precomputation, each in polynomial time.
2. For every species tree $S$ the number of unranked DL-histories of size $n$ is

$$\gamma_S\,\frac{\rho_S^{-n}}{n^{3/2}}\left(1 + O\!\left(\frac{1}{n}\right)\right), \qquad \gamma_S > 0,\ \rho_S \in (0,1/4].$$

For a single species ($k = 1$) the counts are the Catalan numbers; for the caterpillar $\mathrm{CT}_k$ the generating function satisfies $C_k(z) = B(C_{k-1}(z)^2 + C_{k-1}(z) + B(z))$ with $B(z) = z + B(z)^2 = (1-\sqrt{1-4z})/2$ the generating function of binary trees, and the dominant singularity is $\lambda_k = (1 - X_k^2)/4$, where $X_k$ is the minimal positive fixed point of $s_k(X) = X$ for $s_1 = 0$, $s_k(X) = \big((3X-4) - s_{k-1}(X)^2\big)/(X-3)$. For the complete binary tree of height $h$ the singularity is $\mu_h = (1-q_h)/4$ with $q_0 = 0$, $q_{h+1} = (3 - \sqrt{5 - q_h})^2$, an algebraic number of degree $2^h$.
3. In the ranked DLT model in which every speciation is followed by the loss of one copy (Speciation-Loss), the number of histories of size $n$ is the same for every ranked species tree of size $k$.

## Expansion

The grammar mirrors the definition: the first event of a history in species $u$ is a speciation (the gene continues in both children, or is lost in one of them), a duplication (two independent histories in $u$), or a transfer (one history stays in $u$, one starts in an incomparable species). Translating unions and products into sums and products of generating functions gives an algebraic system, solvable by dynamic programming on $(u, n)$ for exact counts and by recursive (Boltzmann-style) generation for uniform sampling. In the DL model each equation is quadratic in $H_u$, so every generating function has a square-root singularity, which gives the universal $n^{-3/2}$ correction and a growth rate at least $4$, the Catalan rate of one branch. With transfers every branch interacts with all incomparable branches, and the exponential growth rates become much larger; in ranked trees the time slices make each slice look the same up to relabelling, and with Speciation-Loss no extra copies cross slice boundaries, which removes the dependence on topology.

## Sources

- Cedric Chauve, Yann Ponty and Michael Wallner, "Counting and sampling gene family evolutionary histories in the duplication-loss and duplication-loss-transfer models", arXiv:1905.04971 (2019), definition of histories (model section), grammar, counting/sampling and asymptotic theorems (methods section), caterpillar and complete-tree propositions and the Speciation-Loss theorem (results and conclusion sections), <https://doi.org/10.48550/arXiv.1905.04971>. Published version: Journal of Mathematical Biology 80 (2020) 1353–1388, <https://doi.org/10.1007/s00285-019-01465-x>.
