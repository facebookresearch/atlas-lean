# At a two-parent node the inheritance probabilities are γ and 1 − γ

Let $N$ be a [phylogenetic network](phylo-network.md) on a finite set $V$ of nodes, with root
$\rho$, parent sets $\mathrm{pa}(v)$ and [inheritance probabilities](inherit.md) $\gamma(v, u)$. If
a node $v$ has exactly the two parents $u_1 \ne u_2$, $\mathrm{pa}(v) = \{u_1, u_2\}$, then
$\gamma(v, u_2) = 1 - \gamma(v, u_1)$. This is the phylogenetic-network instance, a special case, of
the [complementary proportions at a two-parent node](prop-eq-one-sub-of-parents-eq-pair.md) of
admixture graphs.
