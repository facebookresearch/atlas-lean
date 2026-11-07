# Uniform return-probability gap for transient Cayley graphs

For every natural number
$k > 1$ there is a real number $C < 1$ such that for every group $G$ and every $k$-regular Cayley
graph $\Gamma$ on $G$ whose return probability is less than $1$, the return probability of
$\Gamma$ is at most $C$.

This follows from Tessera and Tointon, Corollary 1.3: there is a universal $c > 0$ such that
simple random walk on every connected, locally finite, vertex-transitive graph is recurrent or
escapes with probability at least $c$, so $C = 1 - c$ works for every $k$.

## Sources

- Romain Tessera and Matthew Tointon, Sharp relations between volume growth, isoperimetry and escape probability in vertex-transitive graphs, arXiv preprint (2020, v2 2024), arXiv:2001.01467, https://arxiv.org/abs/2001.01467. Moved from `OpenConjectures/GraphTheory/AMR11Problem33`.
