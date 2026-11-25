# Product-form stationary distribution of a Gordon–Newell network

Consider $N \ge 1$ single-server first-come first-served stations and $K \ge 1$ customers, with no external arrivals or departures. Service times at station $i$ are exponential with rate $\mu_i > 0$, independent of everything else, and on completing service at $i$ a customer moves to station $j$ with probability $p_{ij}$, where $P = (p_{ij})$ is a stochastic matrix, independently of the past. The vector $n = (n_1, \dots, n_N)$ of queue lengths is then a continuous-time Markov chain on $S_K = \{n \in \mathbb{N}^N : n_1 + \dots + n_N = K\}$ whose rate from $n$ to $n - e_i + e_j$, for $j \ne i$ and $n_i \ge 1$, is $\mu_ip_{ij}$. Let $\Lambda$ be a positive solution of $\Lambda_i = \sum_j \Lambda_j p_{ji}$, which exists and is unique up to scaling when $P$ is irreducible. Then $p(n) = G(N,K)^{-1}\prod_i (\Lambda_i/\mu_i)^{n_i}$ on $S_K$, with normalizing constant $G(N,K) = \sum_{m \in S_K}\prod_i (\Lambda_i/\mu_i)^{m_i}$, satisfies the global balance equations of this chain; it is in general not obtained from detailed balance, since the routing need not be reversible. For $N \ge 2$ the queue lengths are not independent: $n_1 = K$ and $n_2 = K$ each have positive probability but cannot occur together.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- Global balance equations of a continuous-time Markov chain on a finite set and their relation to stationary distributions.

## Sources

- O. J. Boxma, *Stochastic Performance Modelling*, lecture notes, Eindhoven University of Technology, January 5, 2017, <https://www.win.tue.nl/~iadan/2WB60/lecturenotes.pdf>, §7.6 (formulas (7.11)–(7.12))
