# Coverability is decidable for Petri nets

There is an algorithm that decides, given an ordinary Petri net $(N, M_0)$ and a marking $M$ of $N$, whether some marking $M' \ge M$ is reachable from $M_0$, since [Petri nets are well-structured transition systems](petri-nets-are-well-structured-transition-systems.md) and coverability is decidable for those, since their predecessor bases are computable ([backward reachability from an upward-closed set stabilizes](backward-reachability-stabilizes.md)). When the net is [connected](../state-machines-marked-graphs-and-free-choice-nets/connected-and-strongly-connected-nets.md) and has at least one place and one transition, the cited lecture notes give a direct algorithm: compute the [coverability graph](coverability-graph-algorithm.md), which is finite, and check whether one of its nodes is $\ge M$.

## Depends on

- [Place/transition Petri nets](../place-transition-petri-nets.md)
- [Reachability set and reachability graph](../reachability-set-and-reachability-graph.md)
- [The coverability graph algorithm](coverability-graph-algorithm.md)
- [Connected and strongly connected nets](../state-machines-marked-graphs-and-free-choice-nets/connected-and-strongly-connected-nets.md)
- [Petri nets are well-structured transition systems](petri-nets-are-well-structured-transition-systems.md)

## Proof depends on

- [The coverability graph construction terminates](coverability-graph-construction-terminates.md)
- [The coverability graph characterizes coverable markings](coverability-graph-characterizes-coverability.md)
- [Petri nets are well-structured transition systems](petri-nets-are-well-structured-transition-systems.md)
- [Coverability is decidable for well-structured transition systems](../../../../Logic/temporal-logic/timed-and-infinite-state-verification/coverability-is-decidable-for-well-structured.md)
- [Backward reachability from an upward-closed set stabilizes](backward-reachability-stabilizes.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, the coverability problem (Section 2.10, p. 38), Theorems 3.2.5 and 3.2.8 and the paragraph opening Section 3.2.2, pp. 50–55.
- A. Finkel and Ph. Schnoebelen, "Well-structured transition systems everywhere!", *Theoretical Computer Science* 256(1–2):63–92, 2001, Section 6, Theorem 6.1, item 1, and the remark after it ("covering is decidable for them"), p. 77.
