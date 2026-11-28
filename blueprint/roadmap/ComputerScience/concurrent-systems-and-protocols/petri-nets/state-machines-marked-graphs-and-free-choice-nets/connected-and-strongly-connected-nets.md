# Connected and strongly connected nets

Let $N = (P, T, F, W)$ be a [Petri net](../place-transition-petri-nets.md), with nodes $P \cup T$ and arcs $F$. $N$ is *connected* if $(x, y) \in (F \cup F^{-1})^*$ for all nodes $x, y$, that is, the undirected graph on $P \cup T$ with an edge for each arc is connected; and $N$ is *strongly connected* if $(x, y) \in F^*$ for all nodes $x, y$, that is, every node is reachable from every other along arcs. Every strongly connected net is connected, and a net with a single node is strongly connected. A connected net is strongly connected if and only if for every arc $(x, y) \in F$ there is a path of arcs leading from $y$ to $x$. Esparza's notes call $(N, M_0)$ a Petri net only when $N$ is connected and has at least one place and one transition (Definition 1.3.8); pages whose results the notes state only for such Petri nets carry this hypothesis explicitly.

## Depends on

- [Place/transition Petri nets](../place-transition-petri-nets.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, the definition of connected and strongly connected nets, the remarks after it, and Proposition 1.2.4(2), Section 1.2, p. 14, and Definition 1.3.8 (Petri nets), p. 16.
