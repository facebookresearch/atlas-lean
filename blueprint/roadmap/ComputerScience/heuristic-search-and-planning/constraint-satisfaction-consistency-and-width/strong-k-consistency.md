# Strong k-consistency

Let a constraint network have variables with finite domains and constraints on subsets of variables.
For $j \ge 2$ the network is $j$-consistent if, for every set of $j - 1$ distinct variables, every
assignment to them that satisfies all constraints among them extends to any further variable by a value
satisfying all constraints among the $j$ variables; it is $1$-consistent if every
variable has a value satisfying its unary constraints, which in particular requires a nonempty domain.
The network is strongly $k$-consistent if it is $j$-consistent for every $j \le k$. For binary networks in
which every domain is nonempty and node consistency holds (every domain value satisfies the unary
constraints), arc consistency coincides with strong $2$-consistency; without the node-consistency and nonempty-domain conditions they differ (an isolated
variable with empty domain is vacuously arc consistent but not $1$-consistent).

## Expansion

This node states a precise definition. A good expansion adds a page for the pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: constraint networks with finite domains and constraints of arbitrary arity given as relations (tables) on their scopes, with their primal (constraint) graph.

## Depends on

- [Binary constraint satisfaction problem](../ac-3-algorithm/binary-csp.md)

## Related topics

- [Constraint graph, orderings and width](constraint-graph-orderings-and-width.md)

## Sources

- V. Kumar, *Algorithms for constraint-satisfaction problems: a survey*, AI Magazine 13(1) (1992) 32–44: $K$-consistency and strong $K$-consistency (p. 36). The survey states that node consistency is strong $1$-consistency and arc consistency is strong $2$-consistency without the domain conditions above. <http://cse.unl.edu/~choueiry/Documents/kumar-survey.pdf>
