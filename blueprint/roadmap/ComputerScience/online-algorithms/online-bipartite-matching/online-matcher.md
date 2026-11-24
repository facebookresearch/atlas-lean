# Deterministic online bipartite matching algorithm

A deterministic online bipartite
matching algorithm with $a$ offline (left) vertices $0, \dots, a - 1$ is given by a proposal
rule: on each arrival it receives the neighbour lists (lists of left vertices) of all earlier
arrivals, in order, and the neighbour list of the current arrival, and proposes a left vertex to
match the arrival to, or none.
