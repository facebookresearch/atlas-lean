# Real Zeckendorf expansions

Let $L = (e_1, \dots, e_N)$ be a list of natural numbers with
$N \ge 2$ and $e_1 \ne 0$, and let $E^*$ be its $L^*$-collection; indices of coefficient functions
and sequences start at $0$. There is a unique strictly decreasing sequence $(Q_m)_{m \ge 0}$ in
$(0, 1)$ such that $\varepsilon \mapsto \sum_k \varepsilon_k Q_k$ is a bijection from $E^*$ onto
$(0, 1)$. Moreover, every such sequence $Q$ has the following properties: for
$\varepsilon, \delta \in E^*$, $\varepsilon \lt _d \delta$ (that is, $\varepsilon_k < \delta_k$ at
the smallest index $k$ where $\varepsilon$ and $\delta$ differ) if and only if
$\sum_k \varepsilon_k Q_k < \sum_k \delta_k Q_k$; for every $m$, $Q_m = \sum_k \bar\beta_k Q_k$,
where $\bar\beta$ is the maximal $L^*$-block starting at index $m + 1$; and if $\omega > 0$
satisfies $-1 + \sum_{k=1}^{N-1} e_k \omega^k + (1 + e_N) \omega^N = 0$, then
$Q_m = \omega^{m+1}$ for every $m$.

## Sources

- Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25, Theorem 6 (`integers-2025-A25-thm-6`; arXiv:2308.12872v1, Section 2.3, quoting Chang 2021).
