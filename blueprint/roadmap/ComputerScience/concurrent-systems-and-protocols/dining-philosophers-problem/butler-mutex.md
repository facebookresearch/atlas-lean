# Mutual exclusion under a butler

In the dining philosophers transition system of the
naive protocol under a butler, for each philosopher $i \in \{0, 1, 2\}$, in no state reachable
from the initial state (all three philosophers thinking) do philosopher $i$ and its neighbour
$i + 1$ (modulo $3$) both eat.
