# Lenzen's deterministic constant-round routing and sorting in the congested clique

In the congested clique, suppose every processor is the source of at most $n$ messages and the destination of at most $n$ messages, each of $O(\log n)$ bits, with destinations known to the sources. There is a deterministic algorithm delivering all messages in $O(1)$ rounds. Moreover, if every processor holds $n$ keys of $O(\log n)$ bits, there is a deterministic $O(1)$-round algorithm after which processor $i$ holds the keys of ranks $(i - 1) n + 1, \dots, i n$ in the global sorted order; consequently selection and computing modes take $O(1)$ rounds.

## Proof sketch

Route in two phases via intermediate processors as in Valiant's scheme, but choose the intermediate assignment deterministically: group messages by source and destination blocks of size $\sqrt n$, and use an edge colouring of a bipartite multigraph of bounded degree (König's theorem) computed locally by each group to balance load, so that every link carries $O(1)$ messages per round. Sorting samples splitters, routes keys to buckets with the routing primitive, and sorts buckets locally, again with a constant number of routing invocations.

## Depends on

- [The congested clique model](the-congested-clique-model.md)

## Proof depends on

- [The congested clique model](the-congested-clique-model.md)

## Sources

- C. Lenzen, "Optimal Deterministic Routing and Sorting on the Congested Clique", PODC 2013, arXiv:1207.1852.
