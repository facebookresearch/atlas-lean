# Asynchronous common subset

In the asynchronous model with $n$ processes, at most $t$ Byzantine, each process $i$ has an input value $x_i$. A protocol solves asynchronous common subset (ACS) if every correct process outputs a set $\mathcal{S}$ of pairs $(j, x_j)$ such that: all correct processes output the same set (agreement); $\lvert \mathcal{S} \rvert \ge n - t$ (validity); $\mathcal{S}$ contains the inputs of at least $n - 2t$ correct processes, and for each correct $j$ with $(j, y) \in \mathcal{S}$ we have $y = x_j$ (integrity); and every correct process eventually outputs (termination with probability one). Atomic broadcast reduces to repeated ACS by agreeing in each epoch on a common subset of proposed batches and ordering it deterministically.

## Depends on

- [Asynchronous binary Byzantine agreement and common coins](asynchronous-binary-byzantine-agreement.md)
- [Reliable broadcast](../../replication-and-consistency/reliable-broadcast.md)

## Sources

- M. Ben-Or, B. Kelmer, T. Rabin, "Asynchronous Secure Computations with Optimal Resilience", PODC 1994.
- A. Miller, Y. Xia, K. Croman, E. Shi, D. Song, "The Honey Badger of BFT Protocols", ACM CCS 2016.
