# ω-places of the coverability graph can be pumped

Let $(N, M_0)$ be an ordinary Petri net whose net is [connected](../state-machines-marked-graphs-and-free-choice-nets/connected-and-strongly-connected-nets.md) and has at least one place and one transition, and let $M'$ be an [ω-marking](omega-markings.md) that the [coverability graph algorithm](coverability-graph-algorithm.md) adds to its set of nodes. For every $k > 0$ there is a marking $M'_k$ reachable from $M_0$ with $M'_k(s) = M'(s)$ for every normal place $s$ of $M'$ and $M'_k(s) > k$ for every ω-place $s$ of $M'$.

## Depends on

- [The coverability graph algorithm](coverability-graph-algorithm.md)
- [Reachability set and reachability graph](../reachability-set-and-reachability-graph.md)
- [Connected and strongly connected nets](../state-machines-marked-graphs-and-free-choice-nets/connected-and-strongly-connected-nets.md)

## Proof depends on

- [Monotonicity lemma for Petri net firing sequences](monotonicity-lemma-for-firing-sequences.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Lemma 3.2.7 and its proof (induction over the nodes added, repeating the sequence that led to the accelerated marking), pp. 54–55.
