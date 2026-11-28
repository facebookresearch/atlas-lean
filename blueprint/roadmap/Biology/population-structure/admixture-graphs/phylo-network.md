# Phylogenetic network (routing skeleton)

A phylogenetic network on a finite set $V$ of nodes is an [admixture graph](admixture-graph.md) on
$V$ together with node ages. That is, it consists of a root $\rho \in V$, a finite set
$\mathrm{pa}(v) \subseteq V$ of parents for each node $v$, real numbers $\gamma(v, u)$ for
$v, u \in V$, the inheritance probabilities (the admixture proportions of the graph), and ages
$t : V \to \mathbb{R}$, measured backward from the present, such that

- the root has no parent, and every other node has one parent (a tree node) or two parents
  (a reticulation node);
- $\gamma(v, u) \ge 0$ for all $v, u$, and $\gamma(v, u) = 0$ when $u \notin \mathrm{pa}(v)$;
- $\sum_{u \in \mathrm{pa}(v)} \gamma(v, u) = 1$ for every node $v \ne \rho$;
- the parent relation is well founded: there is no infinite sequence $v_0, v_1, \dots$ with
  $v_{i+1} \in \mathrm{pa}(v_i)$ for all $i$;
- a parent is never younger than its child: $t(v) \le t(u)$ whenever $u \in \mathrm{pa}(v)$.

A lineage at $v$ traces back to the parent $u$ with probability $\gamma(v, u)$: this is $1$ at a
tree node, and $\gamma$ and $1 - \gamma$ at a reticulation node. The branch length of an edge from
$u$ to its child $v$ is $t(u) - t(v) \ge 0$; ages are only weakly monotone, so zero-length edges and
constant ages are allowed. This is the routing skeleton of a rooted phylogenetic network with
inheritance probabilities (Yu, Degnan and Nakhleh 2012; Zhang, Ogilvie, Drummond and Stadler 2018;
Solís-Lemus and Ané 2016), without the out-degree bounds, leaf labels or strict time consistency of
the fully binary notion: out-degrees are unrestricted, and tree edges need not advance strictly in
time.
