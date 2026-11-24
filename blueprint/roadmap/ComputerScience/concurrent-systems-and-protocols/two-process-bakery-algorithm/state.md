# State of the two-process bakery algorithm

A state of the bakery algorithm for two processes $p_0$ and $p_1$ consists of, for each process, a
program counter (noncritical section, reading the other ticket, writing its own ticket, leaving the
doorway, waiting for the other's choosing flag, waiting for its turn, critical section, exit), a
Boolean $\mathrm{choosing}$ flag, a natural-number ticket ($0$ when it holds none), and a local
register holding the ticket read from the other process.

It is a separate model of the two-process case, with its own program counters, not the case $N = 2$
of [the state of the bakery algorithm](../bakery-algorithm/state.md) for $N$ processes.
