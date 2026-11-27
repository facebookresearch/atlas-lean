# Alon-Boppana bound

Fix a natural number $d$. For every $\varepsilon > 0$ there is $N_0$ such that for every $n \ge N_0$, every simple graph $G$ on $n$ vertices and every real $\lambda$ for which $G$ is a [spectral expander](is-spectral-expander.md) of degree $d$ with parameter $\lambda$,

$$\lambda \ge \frac{2\sqrt{d - 1}}{d} - \varepsilon$$

(read as $\lambda \ge -\varepsilon$ when $d = 0$): the spectral parameter of large $d$-regular graphs is at least $2\sqrt{d-1}/d - o(1)$ as the number of vertices tends to infinity (S. Vadhan, *Pseudorandomness* (2012), Theorem 4.11, stated there for multigraphs; this is the case of simple graphs; due to Alon and Boppana, with a short proof by A. Nilli, Discrete Math. 91 (1991)).

For $d = 1$ and $d = 2$ the bound is trivial or matches cycles; for $d \ge 3$ it says that the spectral parameter of large $d$-regular graphs cannot be pushed below the spectral radius $2\sqrt{d-1}/d$ of the random walk on the infinite $d$-regular tree. Graphs meeting it are Ramanujan graphs.

## Background

- [Elementary lower bound on the spectral parameter](elementary-spectral-lower-bound.md): the
  weaker bound $\sqrt{(N - d)/(d(N - 1))}$, about $1/\sqrt d$, proved from a single test vector.
- [Bipartite Ramanujan graphs of every degree](exists-bipartite-ramanujan.md): infinite families
  meeting the bound, in the one-sided bipartite sense, exist for every degree $d \ge 3$.
