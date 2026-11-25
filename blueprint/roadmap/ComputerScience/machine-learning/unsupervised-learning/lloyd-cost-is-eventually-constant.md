# Lloyd cost is eventually constant

This node collects the eventual constancy of the $k$-means cost under Lloyd's iteration, as a statement
separate from convergence of the assignments.

## Expansion

A sound expansion has separate pages for:

1. **Cost stabilization.** For any tie rule and empty-cluster policy under which neither step increases the
   cost, the cost sequence is nonincreasing and takes finitely many values, so it is eventually constant.
2. **Assignments need not stabilize.** Points $-1$ and $1$, $k = 2$, both centres at $0$, an empty cluster keeping its
   centre, and ties broken arbitrarily: both points are equidistant from both centres, so a run may send both to
   cluster 1, then both to cluster 2, and so on; the occupied cluster's mean and the empty cluster's centre stay $0$,
   so the assignments alternate forever at constant cost $2$.

## Proof depends on

- [One round of Lloyd's algorithm never increases the cost](k-means-clustering/cost-lloyd-le.md)

## Sources

- A. Blum, J. Hopcroft and R. Kannan, *Foundations of Data Science* (2014 course draft): Lloyd's $k$-means algorithm and the fact that neither step increases the cost (p. 260 of that draft). <http://www.cs.cornell.edu/courses/cs4850/2014sp/book.pdf>
