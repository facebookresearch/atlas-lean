# Maximal independent set in O(log log Delta) rounds of the congested clique

In the congested clique, a maximal independent set of an $n$-vertex input graph of maximum degree $\Delta$ can be computed by a randomized algorithm in $\tilde O(\log\log \Delta)$ rounds with high probability.

## Proof sketch

Simulate the desire-level MIS dynamics of Ghaffari's LOCAL algorithm in compressed form: since the relevant random choices for $O(\sqrt{\log \Delta})$-length phases involve sparse subgraphs, each phase can gather the needed neighbourhoods at a few processors using Lenzen routing and simulate many LOCAL rounds locally. Each phase reduces the effective degree from $\Delta$ to about $\Delta^{\epsilon}$, so $O(\log\log \Delta)$ phases suffice, and the residual graph of small size is solved at one processor.

## Depends on

- [The congested clique model](the-congested-clique-model.md)
- [Luby's maximal independent set algorithm](../../local-distributed-algorithms/luby-s-maximal-independent-set-algorithm.md)

## Proof depends on

- [Lenzen's deterministic constant-round routing and sorting in the congested clique](congested-clique-constant-round-routing.md)
- [Randomized MIS in O(log Delta) + polylog-size deterministic time](../../local-distributed-algorithms/deterministic-colouring-and-mis-in-local-and-congest/randomized-mis-log-delta-shattering.md)

## Sources

- M. Ghaffari, "Distributed MIS via All-to-All Communication", PODC 2017.
