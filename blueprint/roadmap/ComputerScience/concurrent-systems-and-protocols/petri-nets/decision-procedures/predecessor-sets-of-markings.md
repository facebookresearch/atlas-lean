# Predecessor sets of markings

Let $N$ be an ordinary [Petri net](../place-transition-petri-nets.md) with transitions $T$, and let $\mathcal{M}$ be a set of markings of $N$. For $t \in T$ let $\mathrm{pre}(\mathcal{M}, t) = \{M' \mid M' [t\rangle M \text{ for some } M \in \mathcal{M}\}$ and $\mathrm{pre}(\mathcal{M}) = \bigcup_{t \in T} \mathrm{pre}(\mathcal{M}, t)$. Let $\mathrm{pre}^0(\mathcal{M}) = \mathcal{M}$, $\mathrm{pre}^{i+1}(\mathcal{M}) = \mathrm{pre}(\mathrm{pre}^i(\mathcal{M}))$ and $\mathrm{pre}^*(\mathcal{M}) = \bigcup_{i \ge 0} \mathrm{pre}^i(\mathcal{M})$, the set of markings from which some marking of $\mathcal{M}$ is reachable.

## Depends on

- [Place/transition Petri nets](../place-transition-petri-nets.md)
- [Reachability set and reachability graph](../reachability-set-and-reachability-graph.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Definition 3.2.15, p. 61.
