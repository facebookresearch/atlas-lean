# Average distance on a phylogenetic network and its basic invariances

Let $N$ be a rooted or semidirected phylogenetic network on taxon set $X$, with edge lengths $\ell(e) \ge 0$ and hybridization parameters $\gamma(e) \in (0,1)$ on hybrid edges, the parameters of the hybrid edges into each hybrid node summing to $1$; set $\gamma(e) = 1$ on tree edges (Definition 3). The open interval matters: a hybrid edge of weight $0$ never contributes to any distance, so its parameters could not be recovered.

*Up-down paths.* In a rooted network, an up-down path between nodes $u, v$ is a sequence of distinct nodes $u = u_1 \dots u_n = v$ with a node $s = u_i$ such that $u_i \dots u_1$ and $u_i \dots u_n$ are directed paths (Definition 5). In a semidirected network, where tree edges are undirected and may be traversed either way, an up-down path is a path $u_1 \dots u_n$ of distinct nodes, consecutive ones joined by an edge, with no *v-structure*: no segment $u_{j-1} u_j u_{j+1}$ in which $u_j$ is a hybrid node and both $u_{j-1}u_j$ and $u_{j+1}u_j$ are hybrid edges directed into $u_j$ (Definition 6). The two definitions agree on a rooted network and its induced semidirected network (Proposition 1). A path and its reversal are the same up-down path. For a path $p$ write $\ell(p) = \sum_{e \in p} \ell(e)$ and $\gamma(p) = \prod_{e \in p}\gamma(e)$. The **average distance** is

$$d_N(u,v) = \sum_{p \in \mathcal P_{uv}} \gamma(p)\,\ell(p),$$

where $\mathcal P_{uv}$ is the set of up-down paths between $u$ and $v$. Equivalently, $d_N(u,v)$ is the expected $u$–$v$ path length in the random tree obtained by keeping, independently at each hybrid node $h$, one parent edge of $h$ chosen with probabilities $\gamma$; hence $d_N$ satisfies the triangle inequality.

**Proposition (root).** If two rooted networks induce the same semidirected network, their pairwise average distances coincide; the root is not identifiable from average distances.

**Proposition (hybrid zip-up).** Let $h$ be a hybrid node with parents $u_1,\dots,u_n$. If $h$ has a single child $w$, the tip-to-tip average distances depend on $\ell(u_1h),\dots,\ell(u_nh),\ell(hw)$ only through

$$l_h = \ell(hw) + \sum_{i=1}^n \gamma(u_ih)\,\ell(u_ih).$$

Consequently, replacing the parent-edge lengths by $0$ and $\ell(hw)$ by $l_h$ ("zipping up" $h$; first inserting a length-$0$ tree edge below $h$ if $h$ has several children) leaves every tip-to-tip average distance unchanged. Distances involving internal nodes can change: the distance from $h$ to $w$ becomes $l_h$ instead of $\ell(hw)$.

**Proposition (parallel edges).** If all parent edges $e_1,\dots,e_n$ of a hybrid node $h$ join the same two nodes $v$ and $h$, replacing them by a single tree edge $vh$ of length $\sum_i \gamma(e_i)\ell(e_i)$ leaves $d_N$ unchanged.

## Expansion

Every up-down path through $h$ from a tip below $h$ enters $h$ through exactly one parent $u_i$, with weight $\gamma(u_ih)$, and then continues through $hw$; summing over the parent choice collapses the contribution of the edges at $h$ to $\gamma$-weighted averages, giving $l_h$. Up-down paths on a rooted network and on its induced semidirected network coincide (Proposition 1), which gives root invariance.

## Sources

- Jingcheng Xu and Cécile Ané, "Identifiability of local and global features of phylogenetic networks from average distances", Journal of Mathematical Biology (2022), <https://doi.org/10.1007/s00285-022-01847-8>. arXiv:2110.11814. Definitions 3, 5–7 and 9; Propositions 1, 2, 3 and 5.
