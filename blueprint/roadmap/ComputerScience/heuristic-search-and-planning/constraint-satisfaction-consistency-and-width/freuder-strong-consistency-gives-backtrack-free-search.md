# Freuder: strong (w+1)-consistency gives backtrack-free search

Let a binary constraint network have finite, nonempty domains, and let $d$ be an ordering of its
constraint graph of width $w$. If the network is strongly $k$-consistent for some $k > w$, then a
search that assigns the variables in the order $d$, giving each variable a value consistent with all
constraints to the earlier variables, never reaches a variable without such a value; in particular
the network has a solution, found without backtracking.

## Depends on

- [Strong k-consistency](strong-k-consistency.md)
- [Constraint graph, orderings and width](constraint-graph-orderings-and-width.md)

## Sources

- V. Kumar, *Algorithms for constraint-satisfaction problems: a survey*, AI Magazine 13(1) (1992) 32–44, Theorem 1 and the argument after it (p. 36), attributed there to E. C. Freuder, *A sufficient condition for backtrack-free search*, J. ACM 29 (1982) 24–32. Kumar states the existence of a backtrack-free order when $k$ exceeds the width of the graph; the argument shows that every ordering of width $w < k$ is one. <http://cse.unl.edu/~choueiry/Documents/kumar-survey.pdf>
