# Correctness and optimality of Chu-Liu/Edmonds

For every finite digraph $G$, root $r$ and arc costs in a linearly ordered abelian group, the Chu-Liu/Edmonds algorithm returns a spanning in-arborescence of $G$ rooted at $r$ whose cost is at most that of every spanning in-arborescence of $G$ rooted at $r$, and it reports failure exactly when $G$ has no spanning in-arborescence rooted at $r$. Out-arborescences are handled by reversing all arcs.

## Proof sketch

Induction on the number of live vertices, which strictly decreases at each contraction; the exchange lemma shows that the optimal costs of the original and contracted instances differ by exactly the selected cycle cost.

## Depends on

- [The Chu-Liu/Edmonds algorithm](chu-liu-edmonds-algorithm.md)

## Proof depends on

- [Exchange lemma for cycle contraction](contraction-exchange-lemma.md)

## Sources

- Y.-J. Chu and T.-H. Liu, "On the Shortest Arborescence of a Directed Graph", Scientia Sinica 14, 1965.
- J. Edmonds, "Optimum Branchings", Journal of Research of the National Bureau of Standards, Section B 71B(4), 1967.
