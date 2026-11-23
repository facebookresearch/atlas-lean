# Four Point Condition f2 of is Tree

In a drift model carrying the weights of a tree-shaped admixture graph, `f2` satisfies the
four-point condition. Binary loadings alone do not suffice: the square weights `00, 10, 01,
11` are binary but their `f2` violates it. Here the lineages are root-ward paths of one tree,
so for each quartet the edges cannot separate it in two different ways
(`AdmixtureGraph.quartet_compatible_of_isTree`).
