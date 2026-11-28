# Extended cost of a request

Let $w_{t-1}$ and $w_t$ be the work functions before and after the request $r_t$ of a $k$-server instance on a metric space $(M, d)$, both defined on configurations $X \in M^k$ (multisets of $k$ points). The *extended cost* of $r_t$ is $\mathrm{ext}_t = \sup_{X} \big(w_t(X) - w_{t-1}(X)\big) \in [0, \infty]$, a maximum when $M$ is finite. Since $w_t(X) \ge w_{t-1}(X)$ for all $X$, extended costs are nonnegative. Telescoping the pointwise increments gives $w_T(X) - w_0(X) = \sum_{t=1}^{T} \big(w_t(X) - w_{t-1}(X)\big) \le \sum_{t=1}^{T} \mathrm{ext}_t$ for every configuration $X$, hence $\sup_X \big(w_T(X) - w_0(X)\big) \le \sum_{t=1}^{T} \mathrm{ext}_t$. A difference of maxima need not exist: on $M = \mathbb{R}$ with $k = 1$ and initial position $0$, $w_0(x) = |x|$ has no maximum.

## Depends on

- [Work functions and the work function algorithm](../paging-and-k-server/work-functions-and-the-work-function-algorithm.md)

## Sources

- Elias Koutsoupias, Christos H. Papadimitriou, "On the k-Server Conjecture", Journal of the ACM 42(5) (1995).
