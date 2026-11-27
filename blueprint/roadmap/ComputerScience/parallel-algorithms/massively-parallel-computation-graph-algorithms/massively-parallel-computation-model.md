# The massively parallel computation model

In the massively parallel computation (MPC) model with input size $N$ and local memory $S$ (bits) per machine, there are $M \ge N/S$ machines, so the *global memory* $M \cdot S$ is at least the input size. The global memory is a separate parameter: the near-linear regime $M \cdot S = \tilde O(N)$ is the one algorithms usually aim for, while other results, such as conditional lower bounds, allow any $\mathrm{poly}(N)$ global memory. Computation proceeds in synchronous rounds: in each round every machine performs local computation on its memory, then sends messages to other machines, with the constraint that each machine sends and receives messages of total size $O(S)$ in a round. For graph problems with $n$ vertices and $m$ edges ($N = O(m + n)$), the local-memory regimes are strongly superlinear memory ($S = n^{1 + \varepsilon}$), near-linear memory ($S = \tilde O(n)$) and strongly sublinear memory ($S = n^{\alpha}$ for a constant $\alpha \in (0, 1)$). The complexity measure is the number of rounds.

## Sources

- H. Karloff, S. Suri, S. Vassilvitskii, "A Model of Computation for MapReduce", SODA 2010.
- P. Beame, P. Koutris, D. Suciu, "Communication Steps for Parallel Query Processing", PODS 2013; Journal of the ACM 64(6) (2017).
- M. Ghaffari, F. Kuhn, J. Uitto, "Conditional Hardness Results for Massively Parallel Computation from Distributed Lower Bounds", FOCS 2019, Section 1.1.
