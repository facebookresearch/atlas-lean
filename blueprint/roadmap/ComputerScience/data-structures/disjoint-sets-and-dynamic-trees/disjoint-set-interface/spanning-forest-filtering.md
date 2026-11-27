# Spanning-forest filtering with a disjoint-set structure

For a graph on $[n]$ given as an edge list $e_1, \dots, e_m$, keep exactly the edges $e_j = \{x, y\}$ for which $\mathrm{union}(x, y)$ reports a merge, processing the edges in order. The kept edges form a sublist $F$ of the edge list, they generate the same equivalence relation (connectivity) as all edges, and $\mathrm{numComponents} + |F| = n$ at the end; applying the filter again to $F$ keeps all of $F$. Hence $F$ is a spanning forest. With union by rank and path compression, the filter runs in $O((n + m)\, \alpha(m, n))$ time, where $\alpha$ is the inverse Ackermann function of Tarjan and van Leeuwen.

## Proof sketch

A union merges two classes exactly when its endpoints were in different components, so each kept edge reduces the number of components by one and never closes a cycle, while each skipped edge joins already connected vertices. The filter makes $n$ make-sets and $m$ unions, that is $2m$ finds, so the Tarjan–van Leeuwen bound $O(n + 2m\,\alpha(2m + n, n))$ applies, and $\alpha(2m+n, n) \le \alpha(m, n)$ because $\alpha$ is nonincreasing in its first argument.

## Depends on

- [Representation-independent disjoint-set interface](disjoint-set-interface.md)
- [Spanning forest of an input graph](../../../graph-algorithms/spanning-trees-flows-matchings/kruskal-s-algorithm/is-spanning-forest.md)

## Proof depends on

- [Tarjan–van Leeuwen bound for union by rank with path compression](../disjoint-set-data-structure/run-empty-cost-le-inverse-ackermann.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
- R. E. Tarjan, "Efficiency of a Good But Not Linear Set Union Algorithm", Journal of the ACM 22(2), pp. 215-225, 1975.
- R. E. Tarjan and J. van Leeuwen, "Worst-Case Analysis of Set Union Algorithms", Journal of the ACM 31(2), pp. 245-281, 1984.
