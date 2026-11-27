# König's lemma for finitely branching graphs

Let $G$ be a directed graph in which every node has finitely many immediate successors, and let $v_0$ be a node from which infinitely many nodes are reachable. Then $G$ contains an infinite path $v_0 v_1 v_2 \cdots$ of pairwise distinct nodes. In particular, if the [reachability graph](../reachability-set-and-reachability-graph.md) of a Petri net $(N, M_0)$ has infinitely many nodes, it contains an infinite path of pairwise distinct markings starting at $M_0$, since each marking has at most one immediate successor per transition.

The graph form follows from [Kőnig's lemma for inverse systems](../../../process-calculi/csp-semantic-models/konig-s-lemma-for-inverse-systems.md), a different statement: take for $\alpha_i$ the set of paths of $i$ pairwise distinct nodes beginning with $v_0$, and for $\pi_{ij}$ the prefix maps. Each $\alpha_i$ is nonempty, since only finitely many nodes lie within $i$ steps of $v_0$, and each path has finitely many one-node extensions.

## Depends on

- [Reachability set and reachability graph](../reachability-set-and-reachability-graph.md)
- [Kőnig's lemma for inverse systems](../../../process-calculi/csp-semantic-models/konig-s-lemma-for-inverse-systems.md)

## Proof depends on

- [Kőnig's lemma for inverse systems](../../../process-calculi/csp-semantic-models/konig-s-lemma-for-inverse-systems.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Lemma 3.2.1 ("Königs lemma") and its proof, which uses only that each node has finitely many immediate successors, p. 48–49; and the proof of Theorem 3.2.5, which applies the lemma to the finitely branching coverability graph, p. 52.
