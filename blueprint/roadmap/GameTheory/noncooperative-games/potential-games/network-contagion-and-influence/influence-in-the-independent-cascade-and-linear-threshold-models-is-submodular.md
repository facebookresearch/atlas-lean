# Influence in the independent cascade and linear threshold models is submodular

In the independent cascade model the influence function $\sigma(S)$ equals the expectation, over random live-edge subgraphs in which each edge is kept independently with its probability, of the number of vertices reachable from $S$. Hence $\sigma$ is a nonnegative combination of coverage functions and is monotone and submodular. The same holds for the linear threshold model, using live-edge graphs in which each vertex keeps at most one incoming edge.

## Proof sketch

Flip all edge coins upfront; the final active set from $S$ is the reachability closure of $S$ in the live-edge graph, and reachability counts are monotone submodular set functions.

## Depends on

- [General threshold, linear threshold and cascade models of influence](general-threshold-linear-threshold-and-cascade-models-of-influence.md)
- [Submodular set function](../../../../ComputerScience/approximation-algorithms/maximum-n-times-coverage/is-submodular.md)

## Sources

- David Kempe, Jon Kleinberg and Eva Tardos, "Maximizing the Spread of Influence through a Social Network", Proceedings of the Ninth ACM SIGKDD International Conference on Knowledge Discovery and Data Mining, 2003.
- Jon Kleinberg, "Cascading Behavior in Networks: Algorithmic and Economic Issues", Algorithmic Game Theory, Cambridge University Press, 2007.
