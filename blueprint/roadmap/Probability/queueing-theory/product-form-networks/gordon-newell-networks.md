# Product-form stationary distribution of a Gordon–Newell network

With $N \ge 1$ stations, no external arrivals, routing that keeps all $K$ customers in the network, and a positive solution $\Lambda$ of $\Lambda_i = \sum_j \Lambda_j p_{ji}$ (which exists and is unique up to scaling when the routing chain is irreducible), the distribution $p(n) = G(N,K)^{-1}\prod_i (\Lambda_i/\mu_i)^{n_i}$ on $\{n : n_1 + \dots + n_N = K\}$ satisfies the global balance equations; it is in general not obtained from detailed balance, since the routing need not be reversible. For $N \ge 2$ and $K \ge 1$ the queue lengths are then not independent: $n_1 = K$ and $n_2 = K$ each have positive probability but cannot occur together.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- Global balance equations of a continuous-time Markov chain on a finite set and their relation to stationary distributions.

## Sources

- O. J. Boxma, *Stochastic Performance Modelling*, lecture notes, Eindhoven University of Technology, January 5, 2017, <https://www.win.tue.nl/~iadan/2WB60/lecturenotes.pdf>, §7.6 (formulas (7.11)–(7.12))
