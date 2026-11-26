# Average distance on a phylogenetic network and its basic invariances

Let $N$ be a rooted or semidirected phylogenetic network on taxon set $X$, with edge lengths $\ell(e) \ge 0$ and hybridization parameters $\gamma(e) \in [0,1]$ on hybrid edges, the parameters of the partner hybrid edges into each hybrid node summing to $1$, and $\gamma(e) = 1$ on tree edges. An *up-down path* between nodes $u,v$ is a path $u = u_1 \dots u_n = v$ with a node $s = u_i$ such that $u_i \dots u_1$ and $u_i \dots u_n$ are directed paths. For a path $p$ write $\ell(p) = \sum_{e \in p} \ell(e)$ and $\gamma(p) = \prod_{e \in p}\gamma(e)$. The **average distance** is
$$d_N(u,v) = \sum_{p \in \mathcal P_{uv}} \gamma(p)\,\ell(p),$$
where $\mathcal P_{uv}$ is the set of up-down paths between $u$ and $v$. Equivalently, $d_N(u,v)$ is the expected $u$–$v$ path length in the random tree obtained by keeping, independently at each hybrid node $h$, one parent edge of $h$ chosen with probabilities $\gamma$; hence $d_N$ satisfies the triangle inequality.

**Proposition (root).** If two rooted networks induce the same semidirected network, their pairwise average distances coincide; the root is not identifiable from average distances.

**Proposition (hybrid zip-up).** Let $h$ be a hybrid node with parents $u_1,\dots,u_n$. If $h$ has a single child $w$, the tip-to-tip average distances depend on $\ell(u_1h),\dots,\ell(u_nh),\ell(hw)$ only through
$$l_h = \ell(hw) + \sum_{i=1}^n \gamma(u_ih)\,\ell(u_ih).$$
Consequently, replacing the parent-edge lengths by $0$ and $\ell(hw)$ by $l_h$ ("zipping up" $h$; first inserting a length-$0$ tree edge below $h$ if $h$ has several children) leaves all average distances unchanged.

**Proposition (parallel edges).** If all parent edges $e_1,\dots,e_n$ of a hybrid node $h$ join the same two nodes $v$ and $h$, replacing them by a single tree edge $vh$ of length $\sum_i \gamma(e_i)\ell(e_i)$ leaves $d_N$ unchanged.

## Expansion

Every up-down path through $h$ from a tip below $h$ enters $h$ through exactly one parent $u_i$, with weight $\gamma(u_ih)$, and then continues through $hw$; summing over the parent choice collapses the contribution of the edges at $h$ to $\gamma$-weighted averages, giving $l_h$. Up-down paths on a rooted network and on its induced semidirected network coincide, which gives root invariance.

## Sources

- Jingcheng Xu and Cécile Ané, "Identifiability of local and global features of phylogenetic networks from average distances", Journal of Mathematical Biology (2022), <https://doi.org/10.1007/s00285-022-01847-8>. arXiv:2110.11814. Definitions 5–7 and 9; Propositions 1, 2, 3 and 5.
