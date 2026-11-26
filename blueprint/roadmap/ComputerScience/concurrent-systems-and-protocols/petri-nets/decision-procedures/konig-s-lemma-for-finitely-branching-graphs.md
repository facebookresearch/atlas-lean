# König's lemma for finitely branching graphs

Let $G$ be a directed graph in which every node has finitely many immediate successors, and let $v_0$ be a node from which infinitely many nodes are reachable. Then $G$ contains an infinite path $v_0 v_1 v_2 \cdots$ of pairwise distinct nodes. In particular, if the [reachability graph](../reachability-set-and-reachability-graph.md) of a Petri net $(N, M_0)$ has infinitely many nodes, it contains an infinite path of pairwise distinct markings starting at $M_0$, since each marking has at most one immediate successor per transition.

## Depends on

- [Reachability set and reachability graph](../reachability-set-and-reachability-graph.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Lemma 3.2.1 ("Königs lemma") and its proof, which uses only that each node has finitely many immediate successors, p. 48–49; and the proof of Theorem 3.2.5, which applies the lemma to the finitely branching coverability graph, p. 52.
