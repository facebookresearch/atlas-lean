# S-components of a net

Let $N$ be an ordinary [Petri net](../place-transition-petri-nets.md). A subnet $N' = (P', T', F')$ of $N$, with $F' = F \cap ((P' \times T') \cup (T' \times P'))$, is an *S-component* if it is a strongly connected [state machine](../subclasses-of-petri-nets.md) and $T' = {}^\bullet P' \cup P'^\bullet$. For every S-component with places $P'$ and every marking $M$ reachable from $M_0$, $M(P') = M_0(P')$.

## Depends on

- [State machines, marked graphs and free-choice nets](../subclasses-of-petri-nets.md)
- [Reachability set and reachability graph](../reachability-set-and-reachability-graph.md)
- [Connected and strongly connected nets](connected-and-strongly-connected-nets.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Definitions 1.2.2 (subnets) and 5.3.11, and Proposition 5.3.12 with its proof, pp. 13 and 113.
- J. Desel and J. Esparza, *Free Choice Petri Nets*, Cambridge Tracts in Theoretical Computer Science 40, Cambridge University Press, 1995, author's copy <https://www.model.in.tum.de/~esparza/fcbook-middle.pdf>, Definition 5.1 and Proposition 5.2(2) (the token count of an S-component of any net is constant on reachable markings), pp. 89–91.
