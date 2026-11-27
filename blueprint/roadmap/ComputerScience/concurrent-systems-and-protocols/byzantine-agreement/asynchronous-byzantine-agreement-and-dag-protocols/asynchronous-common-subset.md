# Asynchronous common subset

In the asynchronous model with $n$ processes, at most $t$ Byzantine, each process $i$ has an input value $x_i$. A protocol solves asynchronous common subset (ACS) if every correct process outputs a set $\mathcal{S}$ of pairs $(j, x_j)$ such that: all correct processes output the same set (agreement); $\lvert \mathcal{S} \rvert \ge n - t$ (validity); $\mathcal{S}$ contains the inputs of at least $n - 2t$ correct processes, and for each correct $j$ with $(j, y) \in \mathcal{S}$ we have $y = x_j$ (integrity); and every correct process eventually outputs (termination with probability one). Repeating ACS and ordering each output deterministically yields a common total order, but not by itself the liveness of atomic broadcast: the at most $t$ missing inputs may be those of the same correct sender in every epoch, whose transactions would then never be ordered. Atomic broadcast from ACS therefore also needs a dissemination and fair-inclusion rule. In HoneyBadgerBFT every correct process keeps unconfirmed transactions in its queue, proposes a random selection of $B/n$ of the first $B$ of them, and encrypts its proposal with threshold encryption until the subset is fixed; a transaction input to $n - t$ correct processes is then committed within a bounded expected number of epochs (censorship resilience, Theorem 4). The guarantee concerns inputs of correct processes; the contributions of Byzantine processes in $\mathcal{S}$ are arbitrary values.

## Depends on

- [Asynchronous binary Byzantine agreement and common coins](asynchronous-binary-byzantine-agreement.md)
- [Reliable broadcast](../../replication-and-consistency/reliable-broadcast.md)

## Sources

- M. Ben-Or, B. Kelmer, T. Rabin, "Asynchronous Secure Computations with Optimal Resilience", PODC 1994.
- A. Miller, Y. Xia, K. Croman, E. Shi, D. Song, "The Honey Badger of BFT Protocols", ACM CCS 2016, Sections 4.3–4.4 and Theorem 4.
