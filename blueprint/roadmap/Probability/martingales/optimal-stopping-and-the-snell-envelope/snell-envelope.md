# Snell envelope by backward induction

For a reward sequence $(G_n)_{n \in \mathbb{N}}$ of real functions, a filtration
$(\mathcal{G}_n)$, a measure $\mu$ and a horizon $N$, the Snell envelope is defined by $S_n = G_N$
for $n \ge N$ and, for $n < N$, by backward induction,

$$S_n = \max\big(G_n, \mathbb{E}[S_{n+1} \mid \mathcal{G}_n]\big).$$

After the horizon the sequence is frozen at $G_N$. The definition accepts arbitrary rewards; when
$\mu$ is finite and the rewards are adapted and integrable, the freezing keeps $S$ a
[supermartingale](supermartingale-snell-envelope.md) on all of $\mathbb{N}$. The book only defines it
for $0 \le n \le N$.

## Sources

- G. Peskir and A. Shiryaev, *Optimal Stopping and Free-Boundary Problems*, Lectures in Mathematics ETH Zürich, Birkhäuser, 2006, Chapter I, §1.1, equations (1.1.6)–(1.1.7).

## Background

- [The dynamic programming policy](../../../ComputerScience/heuristic-search-and-planning/optimality-of-stationary-policies/dp-policy.md): the same backward recursion for a finite Markov decision process.
