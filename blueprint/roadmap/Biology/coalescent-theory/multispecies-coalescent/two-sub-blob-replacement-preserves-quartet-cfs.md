# A degree-2 sub-blob can be replaced by a single edge without changing quartet CFs

Let $\mathcal{N} = (V,E)$ be a rooted or semidirected metric phylogenetic network and let $G$ be the
subgraph induced by a set $W \subset V$ of at least two vertices. Call $G$ **hybrid-closed** if for every
hybrid edge of $G$ all of its partner hybrid edges in $\mathcal{N}$ lie in $G$, let the **boundary**
$\partial G$ be the set of nodes of $W$ adjacent to a node outside $W$, and call $G$ a **$2$-sub-blob** if
it is connected, contains no cut edge of its own, is hybrid-closed, and has exactly two boundary nodes.
For a semidirected network, say that $G$ **traps the root** if the root of every rooted LSA network
inducing it (a rooted network whose root is the lowest stable ancestor of all taxa) lies in
$G \setminus \partial G$. Rooted networks with a root above that ancestor are not counted: everything
above the lowest stable ancestor disappears in the semidirected network, so such a root is not an
outside placement.

Let $G$ be a $2$-sub-blob of $\mathcal{N}$ with boundary nodes $u$ and $v$, and work under the network
multispecies coalescent with correlated inheritance $\mathrm{NMSC}(\rho)$. Then there is a length

$$t = t(G,\rho) \ge -\log(3/2)$$

such that deleting $G$ and inserting a single tree edge $(u,v)$ or $(v,u)$ of length $t$, placing the root
at $u$ or $v$ when the root lay in $G$, leaves every quartet concordance factor of $\mathcal{N}$
unchanged. If $G$ does not trap the root (over rooted LSA networks, as above), or if $u$ (respectively $v$) has a single descendant leaf in
$\mathcal{N} \setminus \{v\}$ (respectively $\mathcal{N} \setminus \{u\}$), then $t \ge 0$.

In the special case where $G$ consists of $m$ parallel edges between $u$ and $v$ with lengths $t_j$ and
inheritance probabilities $\gamma_j$, the replacement length satisfies

$$1 - e^{-t} = \sum_{j=1}^{m} \bigl((1-\rho)\gamma_j^2 + \rho\gamma_j\bigr)\bigl(1 - e^{-t_j}\bigr), \qquad t \ge 0.$$

Consequently, if every non-trivial blob of a metric $4$-taxon network $\mathcal{N}$ has degree at most $2$
and each such $2$-blob $B$ with boundary nodes $u, v$ either does not trap the root in the sense above (over rooted LSA networks) or has a boundary node
with a single descendant leaf in the complement of the other, then $\mathcal{N}$ is neither hard- nor
soft-anomalous.

## Depends on

- [Hard and soft anomalous networks under the network multispecies coalescent](anomalous-networks-under-correlated-inheritance.md)

## Proof depends on

- [Quartet concordance factors do not depend on the root of a network](quartet-cfs-independent-of-the-root.md)

## Expansion

Because $G$ is hybrid-closed and has only two boundary nodes, one of $u, v$ is a hybrid node all of whose
parents lie in $G$, so the inserted edge is a tree edge and the replacement is well defined. Two lineages
entering $G$ either coalesce inside it or leave it separately, and only that probability enters the
quartet concordance factors, so matching it determines $e^{-t}$; allowing a negative length down to
$-\log(3/2)$ is what lets the matching succeed when the blob makes coalescence less likely than any
non-negative tree edge would. The corollary follows because the hypotheses let every blob be replaced by
an edge of non-negative length, reducing the network to a $4$-taxon species tree, and $4$-taxon trees,
binary or star, are not anomalous.

## Sources

- C. Ané, J. Fogg, E. S. Allman, H. Baños and J. A. Rhodes, "Anomalous networks under the multispecies coalescent: theory and prevalence", Journal of Mathematical Biology 88 (2024), 29, <https://doi.org/10.1007/s00285-024-02050-7>. (Definition 6, Theorem 4, Corollary 5.)
