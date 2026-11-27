# The naive protocol can deadlock

Consider the transition system of the naive protocol, in
which every philosopher $i$ picks up fork $i$ first and fork $i + 1$ second (indices modulo $3$),
with atom $i$ read as "philosopher $i$ is eating". Its initial state, where all philosophers are
thinking, satisfies the CTL formula $\mathsf{EF}$ applied to the deadlock formula: from it, a
state in which no philosopher can move is reachable.
