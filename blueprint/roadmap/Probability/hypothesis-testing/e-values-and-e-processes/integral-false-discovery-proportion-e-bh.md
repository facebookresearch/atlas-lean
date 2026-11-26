# E-BH controls the false discovery rate under arbitrary dependence

For e-values $e_1, \dots, e_m$ and a level $\alpha$, let $\hat k$ be the largest $k \le m$ such that at least $k$ of the $e_i$ satisfy $m \le \alpha ke_i$; the e-BH procedure rejects all $i$ with $m \le \alpha\hat ke_i$ (for $\alpha > 0$ and $\hat k \ge 1$, $e_i \ge m/(\alpha\hat k)$; nothing when $\hat k = 0$). If every true-null statistic is an e-value, every false-null statistic is measurable and $\alpha \ge 0$, then the e-BH false discovery proportion is integrable and its expectation, the false discovery rate, is at most $\alpha$.

## Sources

- Wang and Ramdas (2022).
