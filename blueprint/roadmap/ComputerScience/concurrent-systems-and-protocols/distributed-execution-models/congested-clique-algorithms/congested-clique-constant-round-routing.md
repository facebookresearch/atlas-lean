# Lenzen's deterministic constant-round routing and sorting in the congested clique

In the congested clique, suppose every processor is the source of at most $n$ messages and the destination of at most $n$ messages, each of $O(\log n)$ bits, with destinations known to the sources. There is a deterministic algorithm delivering all messages in $O(1)$ rounds. Moreover, if every processor holds $n$ keys of $O(\log n)$ bits, there is a deterministic $O(1)$-round algorithm after which processor $i$ holds the keys of ranks $(i - 1) n + 1, \dots, i n$ in the global sorted order; consequently selection and computing modes take $O(1)$ rounds.

## Proof sketch

The basic primitive is two-round routing with globally known sources and destinations: if every node of a set $W$ sends and receives the same number $f|W|$ of messages, view the messages as edges of a $f|W|$-regular bipartite multigraph from senders to receivers (parallel edges allowed), and decompose it into $f|W|$ perfect matchings by König's theorem. All nodes compute the same decomposition locally; a message in matching $c$ is first sent to node $c$, which then holds exactly $f$ messages for each destination and forwards them directly. Padding with dummy messages handles the "at most" case. For sets of size at most $\sqrt n$, the message counts themselves can be announced by one application of this primitive, so the primitive also works when only the sources know the destinations. Partition the nodes into $\sqrt n$ blocks of size $\sqrt n$. The messages are first redistributed so that each block holds exactly $n$ messages for each block, then within each block so that each node holds exactly $\sqrt n$ messages for each destination block, then sent from each block to each destination block in one round, and finally delivered inside the destination blocks; every step is a constant number of applications of the primitive. Sorting selects and broadcasts splitters, routes keys to buckets with the routing algorithm, and sorts buckets locally, again with a constant number of routing invocations.

## Depends on

- [The congested clique model](the-congested-clique-model.md)

## Proof depends on

- [König's edge coloring theorem for regular bipartite multigraphs](../../../../GraphTheory/graph-coloring/part-01/edge-coloring/k-nig-s-edge-coloring-theorem-for-regula.md)

## Sources

- C. Lenzen, "Optimal Deterministic Routing and Sorting on the Congested Clique", PODC 2013, arXiv:1207.1852, Theorem 3.2, Corollaries 3.3 and 3.4, and Algorithms 1 and 2.
