# The LOCAL model

In the LOCAL model of distributed computing, the network is a graph whose nodes are processors with unique identifiers from a range polynomial in the number $n$ of nodes. Computation proceeds in synchronous rounds; in each round every node sends a message of unbounded size to each neighbour, receives its neighbours' messages and performs an arbitrary local computation. A $t$-round algorithm is one in which every node outputs after $t$ rounds; its complexity is $t$ as a function of $n$.

## Sources

- N. Linial, "Locality in distributed graph algorithms", *SIAM Journal on Computing* 21(1):193–201, 1992
