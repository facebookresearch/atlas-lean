# Amortized update and query cost of a dynamic cell-probe structure

A dynamic cell-probe structure with $w$-bit cells has *amortized update cost* $t_u$ and *amortized query cost* $t_q$ if every sequence of $m_u$ updates and $m_q$ queries, starting from the initial state, is served with at most $m_u t_u + m_q t_q$ cell probes in total (reads and writes, with computation free). For randomized structures the bound is on the expected number of probes, and queries must be correct always (Las Vegas) or with probability at least $1 - n^{-\Omega(1)}$ (Monte Carlo, as in Pătraşcu–Demaine). In Pătraşcu–Demaine tradeoffs, $\lg x$ denotes $\log_2(2 + x)$, which is positive for all $x \ge 0$.

## Depends on

- [The cell-probe model](../range-query-structures/advanced-data-structures/the-cell-probe-model.md)

## Sources

- Mihai Pătraşcu, Erik D. Demaine, "Logarithmic Lower Bounds in the Cell-Probe Model", SIAM Journal on Computing 35(4) (2006), arXiv:cs/0502041.
- Andrew C. Yao, "Should Tables Be Sorted?", Journal of the ACM 28(3) (1981).
