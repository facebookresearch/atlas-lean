# Product-form stationary distribution of a Jackson network

Consider $N \ge 1$ single-server first-come first-served stations; customers arrive from outside at station $i$ according to independent Poisson processes of rates $\lambda_i \ge 0$, service times at station $i$ are exponential with rate $\mu_i > 0$, independent of everything else, and on completing service at $i$ a customer moves to $j$ with probability $p_{ij}$ or leaves with probability $1 - \sum_j p_{ij}$, independently of the past. The vector of queue lengths is then a continuous-time Markov chain. Let $\Lambda \ge 0$ be a nonnegative solution of the traffic equations $\Lambda_i = \lambda_i + \sum_j \Lambda_j p_{ji}$; when every customer eventually leaves (the spectral radius of $P = (p_{ij})$ is below $1$), the unique solution is $\Lambda = \lambda(I - P)^{-1} = \lambda\sum_{k \ge 0} P^k \ge 0$. If $\Lambda_i < \mu_i$ for every $i$, then $p(n) = \prod_i (1 - \rho_i)\rho_i^{n_i}$, $\rho_i = \Lambda_i/\mu_i$, is a probability distribution satisfying the global balance equations of this chain, so in steady state the queue lengths are independent with geometric marginals. Without the sign condition the conclusion fails: with $N = 1$, $\lambda_1 = 0$, $p_{11} = 1$, $\mu_1 = 1$, the value $\Lambda_1 = -1$ solves the traffic equation and satisfies $\Lambda_1 < \mu_1$, but gives negative weights.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- Global balance equations of a continuous-time Markov chain on a countable set and their relation to stationary distributions.
- Non-explosion of the open-network chain (bounded jump rates).

## Sources

- O. J. Boxma, *Stochastic Performance Modelling*, lecture notes, Eindhoven University of Technology, January 5, 2017, <https://www.win.tue.nl/~iadan/2WB60/lecturenotes.pdf>, §7.2 and §7.5 (formulas (7.9)–(7.10))
