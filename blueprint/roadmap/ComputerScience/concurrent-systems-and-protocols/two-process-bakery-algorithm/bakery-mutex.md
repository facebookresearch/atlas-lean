# Mutual exclusion for the two-process bakery algorithm

Run the two processes of the bakery algorithm interleaved, one step of one process at a time, from
the initial state in which both are in their noncritical sections with no tickets, lowered flags and
registers at $0$. On every infinite run, the LTL formula
$\square \neg(\mathit{cs}_0 \wedge \mathit{cs}_1)$ holds, where $\mathit{cs}_i$ says that process
$p_i$ is in its critical section: at no time are both processes in their critical sections.

[Mutual exclusion for the bakery algorithm](../bakery-algorithm/mutual-exclusion.md) states the property
for $N$ processes, on the reachable states of a separate model.
