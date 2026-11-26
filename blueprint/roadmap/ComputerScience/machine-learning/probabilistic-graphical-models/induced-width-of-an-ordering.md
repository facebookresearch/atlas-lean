# Induced width of an ordering

Let $H$ be a finite undirected graph and $d$ an ordering of its vertices. The induced graph $H_d$ is
obtained by processing the vertices from last to first and, when processing $v$, adding edges between
all pairs of neighbours of $v$ that precede $v$ in $d$ (the neighbours in the current graph, including
earlier fill edges). The induced width $w^*(d)$ is the maximum, over vertices $v$, of the number of
neighbours of $v$ in $H_d$ that precede $v$ (zero for a graph with no edges). The minimum of $w^*(d)$
over all orderings equals the tree-width of $H$, the least over tree decompositions of the largest bag size
minus one; with this convention a graph with an edge has tree-width at least $1$. The cited source writes
$w^*$ for that minimum and states it as tree-width minus one, a convention in which tree-width is the
largest bag size.

The equality between the minimum induced width and the tree-width is a theorem, not part of the definition.

## Related topics

- [Tree-width](../../../GraphTheory/planar-graphs-and-minors/tree-width/README.md)

## Sources

- R. Dechter, *Bucket elimination: a unifying framework for reasoning*, Artificial Intelligence 113 (1999) 41–85, Section 2: induced graph, induced width $w^*(d)$ and $w^*$ (p. 46). <http://ics.uci.edu/~dechter/publications/r76A.pdf>
