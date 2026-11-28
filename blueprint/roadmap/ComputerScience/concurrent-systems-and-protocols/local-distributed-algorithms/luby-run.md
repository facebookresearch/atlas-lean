# Running Luby's algorithm

Let $G$ be a graph on $\{0, \dots, n-1\}$ and
let $\pi_1, \dots, \pi_k$ be priority functions on its vertices. The algorithm starts from the
empty independent set and all vertices remaining, and runs one round of Luby's algorithm with the
priorities $\pi_t$ for each $t = 1, \dots, k$ in turn: the remaining vertices whose priority is
smaller than that of every remaining neighbor, ties broken by vertex index, join the independent
set, and they and their neighbors are removed. The result is the pair of the independent set
built and the set of vertices still remaining.
