# Operation bounds for generic push-relabel

Start from the preflow that saturates all arcs out of $s$, with $h(s) = |V|$ and $h \equiv 0$ elsewhere, and apply admissible push and relabel operations in any order. Then the labeling stays valid, every active vertex has a residual path back to $s$, and labels never exceed $2|V| - 1$. Consequently the run performs at most $(|V| - 2)(2|V| - 1)$ relabels, at most $2|V| - 1$ saturating pushes per pair of antiparallel arcs (at most $|V|$ along each arc), and at most $(|V| - 2)(2|V| - 1) + (2|V| - 1)^2|A_s|$ nonsaturating pushes, where $A_s$ is the set of symmetric arc pairs. When no operation applies, the preflow is a maximum flow and the vertices that can reach $t$ residually give a minimum cut.

## Proof sketch

Labels are bounded by residual distance to $s$ plus $|V|$. Saturating pushes on an arc pair must alternate with label increases of $2$; nonsaturating pushes decrease the potential $\sum_{v \text{ active}} h(v)$, which grows only through relabels and saturating pushes.

## Depends on

- [Preflows, valid labelings, push and relabel](preflows-and-valid-labelings.md)
- [Max-flow min-cut theorem](../../../../GraphTheory/matchings-and-flows/max-flow-min-cut-theorem/max-flow-min-cut.md)

## Sources

- A. V. Goldberg and R. E. Tarjan, "A New Approach to the Maximum-Flow Problem", Journal of the ACM 35(4), 1988.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd ed., MIT Press, 2009.
