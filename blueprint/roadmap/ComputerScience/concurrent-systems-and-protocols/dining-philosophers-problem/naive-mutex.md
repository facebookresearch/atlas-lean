# Mutual exclusion under the naive protocol

For every philosopher $i$, in the transition
system of the naive protocol, with atom $j$ read as "philosopher $j$ is eating", the initial
state satisfies $\mathsf{AG}$ applied to the formula that philosophers $i$ and $i + 1$ (indices
modulo $3$) do not both eat: in no state reachable from the initial state, where all
philosophers are thinking, are philosophers $i$ and $i + 1$ both eating.
