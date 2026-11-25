# Cluster of a vertex seen from a leaf

For an [unrooted binary phylogenetic tree](unrooted-binary-tree.md) on a finite set $X$, a taxon $a$ and a vertex $v$, the cluster of $v$ seen from $a$ is the set of taxa $x \ne a$ with

$$\mathrm{dist}(\ell_a, v) + \mathrm{dist}(v, \ell_x) = \mathrm{dist}(\ell_a, \ell_x),$$

where $\ell_x$ is the leaf labeled $x$ and $\mathrm{dist}$ the graph distance: the taxa whose leaf lies beyond $v$ on a path from $\ell_a$.
