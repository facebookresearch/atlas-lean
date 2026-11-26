# The go-back-N protocol

The go-back-N protocol with window size $2$ and sequence
numbers modulo $3$ is the recursive CCS process in its initial configuration: the parallel
composition of the sender with an empty window based at $0$, the empty lossy one-place data
channel, and the receiver expecting $0$, with the internal channels $\mathrm{send}_k$,
$\mathrm{recv}_k$ and $\mathrm{ack}_k$ for $k \in \{0, 1, 2\}$ restricted.
