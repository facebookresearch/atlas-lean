# Extended cost of a request

Let $w_{t-1}$ and $w_t$ be the work functions before and after the request $r_t$ of a $k$-server instance on a metric space $(M, d)$, both defined on configurations $X \in M^k$ (multisets of $k$ points). The *extended cost* of $r_t$ is $\mathrm{ext}_t = \max_{X} \big(w_t(X) - w_{t-1}(X)\big)$. Since $w_t(X) \ge w_{t-1}(X)$ for all $X$, extended costs are nonnegative, and $\sum_{t \le T} \mathrm{ext}_t$ upper-bounds $\max_X w_T(X) - \max_X w_0(X)$.

## Depends on

- [Work functions and the work function algorithm](../paging-and-k-server/work-functions-and-the-work-function-algorithm.md)

## Sources

- Elias Koutsoupias, Christos H. Papadimitriou, "On the k-Server Conjecture", Journal of the ACM 42(5) (1995).
