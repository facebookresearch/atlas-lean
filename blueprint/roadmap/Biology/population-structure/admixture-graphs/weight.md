# Lineage weight of an edge in an admixture graph

In an [admixture graph](admixture-graph.md) with admixture proportions $a$, the lineage weight of an [edge](edge.md) $e = (c, p)$ for a node $X$ is

$$w(X, e) = v(X, c)\, a(c, p),$$

where $v$ is the [visit probability](visit.md): the probability that the lineage of a gene sampled in $X$ reaches $c$ and then descends from $p$.
