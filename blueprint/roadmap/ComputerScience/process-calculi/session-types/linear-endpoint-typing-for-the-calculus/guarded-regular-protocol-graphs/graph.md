# Finite guarded regular protocol graph

A protocol graph is a natural number $m$ (its size) together with a map assigning to each $i \in
\{0, \dots, m-1\}$ a node over $\{0, \dots, m-1\}$: $\mathrm{end}$, a name send or receive with a
successor, or an endpoint send or receive with payload polarity, rank, payload node, orientation
flag and successor. Every node other than $\mathrm{end}$ is an action, so every cycle of the graph
passes through communication actions. A graph of size $0$ has no nodes.
