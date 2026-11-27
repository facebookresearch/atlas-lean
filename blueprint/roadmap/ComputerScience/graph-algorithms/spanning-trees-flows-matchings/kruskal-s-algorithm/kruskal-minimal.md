# Kruskal's algorithm gives a minimum spanning forest

Let $G$ be a graph with
natural-number edge weights, and let $F$ be any spanning forest of $G$: a list of valid edges of
$G$ that is acyclic and connects the endpoints of every valid edge of $G$. Then the total weight
of the edge list returned by Kruskal's algorithm on $G$ is at most the total weight of $F$.

Total weights count parallel edge occurrences separately, and $G$ need not be connected.

## Sources

- CLRS, fourth edition, §21.2, cut-exchange argument.
