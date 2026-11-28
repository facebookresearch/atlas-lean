# Constraint graph, orderings and width

The constraint graph of a binary constraint network has the variables as vertices and an edge
between two variables when some constraint involves both. For an ordering $d$ of the vertices, the width
of a vertex is the number of its neighbours that precede it in $d$, the width of $d$ is the maximum
vertex width (zero for a graph with no vertices or no edges), and the width of the graph is the minimum
width over all orderings. Ordinary width is not the induced width: the induced width of $d$ is computed
after adding fill edges between earlier neighbours (a separate definition), and its minimum over
orderings is the treewidth. Forests have width at most $1$.

## Depends on

- [Binary constraint satisfaction problem](../ac-3-algorithm/binary-csp.md)

## Related topics

- [Induced width of an ordering](../../machine-learning/probabilistic-graphical-models/induced-width-of-an-ordering.md)

## Sources

- V. Kumar, *Algorithms for constraint-satisfaction problems: a survey*, AI Magazine 13(1) (1992) 32–44: width of a vertex, of an ordered constraint graph and of a constraint graph (p. 36); trees have width $1$ (p. 37). <http://cse.unl.edu/~choueiry/Documents/kumar-survey.pdf>
