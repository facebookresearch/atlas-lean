# The optimal threshold is asymptotically $n/e$

The [optimal threshold](optimal-threshold.md) satisfies $r_1(n)/n \to 1/e$ as $n \to \infty$.

Ferguson derives the limit from $\sum_{k=r+1}^{n} 1/(k-1) \sim \log(n/r)$. The proof makes this
quantitative: $\log n - \log r_1 \le T_{r_1} \le 1$ gives $r_1 \ge n/e$, and
$1 < T_{r_1 - 1} \le \log(n-1) - \log(r_1 - 2)$ gives $r_1 \le n/e + 2$.

## Sources

- T. S. Ferguson, *Optimal Stopping and Applications*, online text (UCLA Department of Mathematics), Chapter 2, §2.1, the paragraph after the table.

## Informally uses

- [Integral lower bound for the harmonic tail](log-sub-log-le-harmonic-tail.md)
- [Integral upper bound for the harmonic tail](harmonic-tail-le-log-sub-log.md)
