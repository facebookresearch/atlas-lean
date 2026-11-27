# The massively parallel computation model

In the massively parallel computation (MPC) model with input size $N$ and local memory $S$, there are $M$ machines with $M \cdot S = \tilde O(N)$ total memory. Computation proceeds in synchronous rounds: in each round every machine performs arbitrary local computation on its memory, then sends messages to other machines, with the constraint that the total size of messages sent and received by each machine in a round is at most $S$. For graph problems with $n$ vertices and $m$ edges ($N = m + n$), the regimes are strongly superlinear memory ($S = n^{1 + \varepsilon}$), near-linear memory ($S = \tilde O(n)$) and strongly sublinear memory ($S = n^{\alpha}$ for a constant $\alpha \in (0, 1)$). The complexity measure is the number of rounds.

## Sources

- H. Karloff, S. Suri, S. Vassilvitskii, "A Model of Computation for MapReduce", SODA 2010.
- P. Beame, P. Koutris, D. Suciu, "Communication Steps for Parallel Query Processing", PODS 2013; Journal of the ACM 64(6) (2017).
- M. Ghaffari, F. Kuhn, J. Uitto, "Conditional Hardness Results for Massively Parallel Computation from Distributed Lower Bounds", FOCS 2019.
