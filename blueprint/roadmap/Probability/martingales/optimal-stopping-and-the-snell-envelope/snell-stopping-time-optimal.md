# Optimality of the first meeting time

Let $\mu$ be a finite measure, $(\mathcal{G}_k)$ a filtration, and $(G_k)$ an adapted reward
sequence with every $G_k$ integrable, with [first meeting time](snell-stopping-time.md) $\tau^*$
for the horizon $N$. Then every stopping time $\tau \le N$ satisfies
$\mathbb{E}[G_\tau] \le \mathbb{E}[G_{\tau^*}]$; hence $\tau^*$ is optimal and the value
$\sup_{\tau \le N} \mathbb{E}[G_\tau]$ equals $\mathbb{E}[S_0]$, with $S$ the [Snell
envelope](snell-envelope.md).

In other words, $V^N_0 = \sup_{\tau \le N} \mathsf E\, G_\tau = \mathsf E\, S_0 = \mathsf E\, G_{\tau^*}$: optimal stopping over a finite horizon is solved by backward induction.

## Sources

- G. Peskir and A. Shiryaev, *Optimal Stopping and Free-Boundary Problems*, Lectures in Mathematics ETH Zürich, Birkhäuser, 2006, Chapter I, §1.1, Theorem 1.2 (finite horizon), part (1.1.11) with $n = 0$.

## Informally uses

- [Every bounded stopping time earns at most the expected envelope at time zero](integral-stopped-value-le-integral-snell.md)
- [The first meeting time attains the expected envelope at time zero](integral-stopped-value-snell-stopping-ti.md)

## Background

- [Optimality of the dynamic programming algorithm](../../../ComputerScience/heuristic-search-and-planning/optimality-of-stationary-policies/is-greatest-n-stage-value.md): the analogous optimality of backward induction for finite Markov decision processes (Bertsekas).
- [The optimal threshold rule of the secretary problem](../secretary-problem/win-prob-le-win-prob-optimal-threshold.md): a classical instance of a finite-horizon stopping problem.
