# Tree-diet treewidth reduction

Many RNA bioinformatics algorithms (structure alignment, design, comparison) are fixed-parameter tractable in the treewidth of an input graph. The tree-diet problem trades exactness for speed: delete as few graph edges as possible so that a given tree-decomposition can be thinned to a smaller prescribed width, run the treewidth-based algorithm on the thinner decomposition, and account for the lost edges afterwards.

- [Tree-diet problem and its coloring dynamic program](tree-diet-problem-and-its-coloring-dynamic-program.md)
- [Parameterized complexity of graph, tree and path diets](parameterized-complexity-of-graph-tree-and-path-diets.md)
