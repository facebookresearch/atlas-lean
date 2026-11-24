# Reliability of series, parallel and k-out-of-n systems

Let components $e$ of a finite nonempty system have measurable lifetimes $T_e \ge 0$ on one probability space, with up events $\{T_e > t\}$. (Deterministic structure.) A series system has lifetime $\min_eT_e$ and a parallel system $\max_eT_e$, so $\{T_{\mathrm{ser}} > t\} = \bigcap_e\{T_e > t\}$ and $\{T_{\mathrm{par}} > t\} = \bigcup_e\{T_e > t\}$. (Independence.) If the components are independent with reliabilities $p_e = P(T_e > t)$ at a fixed $t$, the series system works with probability $\prod_ep_e$ and the parallel system with probability $1 - \prod_e(1 - p_e)$; if $n \ge 1$ components are i.i.d. with reliability $p$, a $k$-out-of-$n$ system ($1 \le k \le n$) works with probability $\sum_{j=k}^{n}\binom nj p^j(1-p)^{n-j}$. (Mean time to failure.) For a system lifetime $T \ge 0$, $E[T] = \int_0^\infty P(T > t)\,dt$ in $[0, \infty]$; the value is finite exactly when $T$ is integrable.

## Proof depends on

- [Layer-cake formula](../../../MeasureTheory/integration/layer-cake-formula/README.md): the mean as the integral of the survival function.
