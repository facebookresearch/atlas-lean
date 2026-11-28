# The CONGEST model of distributed computing

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. In the CONGEST model each vertex is a processor that knows its identifier and its incident edges; computation proceeds in synchronous rounds, and in each round every vertex may send a possibly different message of $O(\log n)$ bits to each neighbour, receive its neighbours' messages and perform arbitrary local computation. The round complexity of an algorithm is the number of rounds until every vertex has produced its output. CONGEST differs from the LOCAL model only in the bound on message size, so every $t$-round CONGEST algorithm is a $t$-round LOCAL algorithm, and in $t$ rounds of LOCAL each vertex can learn its entire radius-$t$ neighbourhood.

## Depends on

- [The LOCAL model](../../distributed-execution-models/the-local-model.md)

## Sources

- D. Peleg, "Distributed Computing: A Locality-Sensitive Approach", SIAM Monographs on Discrete Mathematics and Applications (2000).
