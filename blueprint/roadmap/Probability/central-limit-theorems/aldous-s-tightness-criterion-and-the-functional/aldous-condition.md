# Aldous's condition

Let $(\xi_{n,i})$ be a triangular array on a measure space, row $n$ filtered by $(\mathcal F_{n,i})_i$, with partial sums $S_n(k) = \sum_{i<k} \xi_{n,i}$ observed at the times $k/n$. The array satisfies Aldous's condition when for every $\varepsilon, \eta > 0$ there are a window $\theta > 0$ and an $N$ such that for all $n \ge N$ and all $\mathcal F_n$-stopping times $\sigma \le \rho \le \sigma + \lfloor n\theta\rfloor$ with $\rho \le n$, $\mu(|S_n(\rho) - S_n(\sigma)| \ge \varepsilon) \le \eta$, where $\mu$ is the measure of the space (a probability in the applications).

This is the two-stopping-time form of Aldous's condition, written for the grid stopping times of the step process $t \mapsto S_n(\lfloor n t\rfloor)$ on $[0, 1]$. Aldous's original form has a deterministic shift $\delta_n \to 0$ after one stopping time; the two-stopping-time form is the one used to prove tightness.

## Sources

- J. Jacod and A. N. Shiryaev, *Limit Theorems for Stochastic Processes*, 2nd ed., Springer (2003), Theorem VI.4.5 (ii).
- D. Aldous, "Stopping times and tightness", Annals of Probability 6 (1978), 335–340.
