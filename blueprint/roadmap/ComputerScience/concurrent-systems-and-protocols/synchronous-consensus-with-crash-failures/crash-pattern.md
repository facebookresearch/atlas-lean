# Crash pattern

A crash pattern for a set $G$ of processes assigns to each process $j$ either nothing, when $j$ is correct, or a pair $(\rho, D)$ of a round $\rho \in \mathbb{N}$ and a finite set $D \subseteq G$, when $j$ crashes in round $\rho$ and its messages of that round reach exactly the processes of $D$.

This is the crash model of Aguilera and Toueg (1999, §1): a process that crashes in a round sends a subset of the messages it intends to send in that round and does not execute later rounds. A crash in a round $\rho \ge T$, after the decisions, makes the process faulty without changing anything it sends before the end.

## Sources

- M. K. Aguilera, S. Toueg, *A simple bivalency proof that t-resilient consensus requires t + 1 rounds*, Information Processing Letters 71(3–4), 1999, 155–158: §1.
