# Coverability is decidable for Petri nets

There is an algorithm that decides, given an ordinary Petri net $(N, M_0)$ and a marking $M$ of $N$, whether some marking $M' \ge M$ is reachable from $M_0$: compute the coverability graph, which is finite, and check whether one of its nodes is $\ge M$.

## Depends on

- [Place/transition Petri nets](../place-transition-petri-nets.md)
- [Reachability set and reachability graph](../reachability-set-and-reachability-graph.md)

## Proof depends on

- [The coverability graph construction terminates](coverability-graph-construction-terminates.md)
- [The coverability graph characterizes coverable markings](coverability-graph-characterizes-coverability.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, the coverability problem (Section 2.10, p. 38), Theorems 3.2.5 and 3.2.8 and the paragraph opening Section 3.2.2, pp. 50–55.
