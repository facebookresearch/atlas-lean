# The coverability graph algorithm

Let $(N, M_0)$ be an ordinary Petri net and use [ω-markings of a Petri net](omega-markings.md). The algorithm COVERABILITY-GRAPH maintains a graph $(V, E)$ with $V = \{M_0\}$, $E = \emptyset$ and a work set $\{M_0\}$. While the work set is nonempty it removes some $M$ from it and, for each transition $t$ enabled at $M$, computes the ω-marking $M'$ obtained by firing $t$ at $M$ and then applies AddOmegas: for every $M'' \in V$ with $M'' < M'$ from which $M$ is reachable along zero or more edges of $E$, it replaces $M'$ by the ω-marking that is $\omega$ at every place $p$ with $M'(p) > M''(p)$ and agrees with $M'$ at every other place (the source writes this as $M' + (M' - M'') \cdot \omega$). If the resulting $M'$ is not in $V$, it is added to $V$ and to the work set; in every case the edge $(M, t, M')$ is added to $E$. When the work set is empty the algorithm returns $(V, E)$, the *coverability graph* of $(N, M_0)$, rooted at $M_0$.

It differs from [the coverability tree](coverability-tree.md) in merging equal ω-markings into one node and in comparing a new marking with every node from which the current one is reachable.

## Depends on

- [ω-markings of a Petri net](omega-markings.md)
- [The coverability tree](coverability-tree.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Section 3.2.2: the procedures COVERABILITY-GRAPH and AddOmegas of Figure 3.2 (p. 53) and the explanation on pp. 51–52.
