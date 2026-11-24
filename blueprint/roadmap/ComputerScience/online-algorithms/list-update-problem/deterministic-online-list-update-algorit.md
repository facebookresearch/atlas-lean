# Deterministic online list-update algorithm

Let $M$ be a list of items. A deterministic online list-update algorithm on the items of $M$ is a
state machine: a set of states, an initial state, a map assigning to each state $q$ a list that is
a rearrangement (permutation) of $M$, and a step map giving the state reached from $q$ after a
request for an item. Only access costs are charged to such an algorithm; its rearrangements are
free, which only strengthens lower bounds proved against it.
