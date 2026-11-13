# The Chang–Roberts transition system

For identifiers $\mathrm{id}$, the algorithm is the
labelled transition system whose states are the global states and whose labels are processes:
there is a transition from $s$ to $t$ labelled $k$ exactly when delivering the oldest message in
the channel of process $k$ in state $s$ gives $t$.
