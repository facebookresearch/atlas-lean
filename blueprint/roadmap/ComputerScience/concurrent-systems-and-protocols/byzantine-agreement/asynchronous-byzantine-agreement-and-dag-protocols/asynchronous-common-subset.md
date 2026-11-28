# Asynchronous common subset

In the asynchronous model with $n$ processes, at most $t$ Byzantine, each process $i$ has an input value $x_i$. A protocol solves asynchronous common subset (ACS) if its outputs, sets $\mathcal{S}$ of pairs $(j, x_j)$, satisfy: if a correct process outputs $\mathcal{S}$, then $\lvert \mathcal{S} \rvert \ge n - t$ and $\mathcal{S}$ contains the inputs of at least $n - 2t$ correct processes (validity); if a correct process outputs $\mathcal{S}$, then every correct process outputs $\mathcal{S}$ (agreement); and if $n - t$ correct processes receive an input, then all correct processes produce an output (totality). Repeating ACS and ordering each output deterministically yields a common total order, but not by itself the liveness of atomic broadcast: the at most $t$ missing inputs may be those of the same correct sender in every epoch, whose transactions would then never be ordered. Atomic broadcast from ACS therefore also needs a dissemination and fair-inclusion rule. In HoneyBadgerBFT every correct process keeps unconfirmed transactions in its queue, proposes a random selection of $B/n$ of the first $B$ of them, and encrypts its proposal with threshold encryption until the subset is fixed; if a transaction is input to $n - t$ correct processes and $T$ is the backlog, the total number of transactions previously input to any correct process minus the number already committed, then the transaction is committed within $O(T/B + \lambda)$ epochs, for security parameter $\lambda$, except with negligible probability (censorship resilience, Theorem 4). The guarantee concerns inputs of correct processes; the contributions of Byzantine processes in $\mathcal{S}$ are arbitrary values.

## Depends on

- [Asynchronous binary Byzantine agreement and common coins](asynchronous-binary-byzantine-agreement.md)
- [Reliable broadcast](../../replication-and-consistency/reliable-broadcast.md)

## Sources

- M. Ben-Or, B. Kelmer, T. Rabin, "Asynchronous Secure Computations with Optimal Resilience", PODC 1994.
- A. Miller, Y. Xia, K. Croman, E. Shi, D. Song, "The Honey Badger of BFT Protocols", ACM CCS 2016, IACR ePrint 2016/199, Section 4.3 (definition of ACS: validity, agreement, totality), Section 4.4 and Theorem 4.
