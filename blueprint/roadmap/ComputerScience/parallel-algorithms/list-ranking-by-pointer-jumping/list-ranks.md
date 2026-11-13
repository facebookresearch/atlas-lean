# List ranking by pointer jumping

For a successor map $\mathrm{succ}$ on the nodes
$0, \dots, n-1$, list ranking by pointer jumping runs $\lceil \log_2 n \rceil$ rounds of pointer
jumping on arrays, starting from the initial state, and returns the resulting array of distances,
whose entry $v$ is the distance of node $v$.

When the lists terminate, entry $v$ is the rank of node $v$.
