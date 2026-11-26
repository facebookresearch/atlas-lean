# Total extended cost is at most $2k \cdot \mathrm{OPT}$

For every $k$-server instance on any metric space, $\sum_{t=1}^T \mathrm{ext}_t \le 2k \cdot \mathrm{OPT}_T + c_1$ for all $T$, where $c_1$ depends only on the initial configuration and the metric restricted to the requested points.

## Proof sketch

Koutsoupias and Papadimitriou use quasiconvexity to prove the *duality lemma*: the extended cost of $r_t$ is attained at a configuration $A$ that minimizes $w_{t-1}(A) - \sum_{a \in A} d(r_t, a)$, so that the maximizers of $w_t - w_{t-1}$ are controlled by a potential $\Phi(w) = \max_{A, B_1, \dots, B_k}$ of a combination of work-function values and distances. The potential increases by at least $\mathrm{ext}_t$ minus $2k$ times the increase of $\min w$, and it is bounded in terms of $(2k)\,\mathrm{OPT}_T$ at the end, which yields the bound.

## Depends on

- [Quasiconvexity of work functions](work-function-quasiconvexity.md)
- [Extended cost of a request](extended-cost.md)

## Proof depends on

- [Quasiconvexity of work functions](work-function-quasiconvexity.md)
- [Extended cost of a request](extended-cost.md)

## Sources

- Elias Koutsoupias, Christos H. Papadimitriou, "On the k-Server Conjecture", Journal of the ACM 42(5) (1995).
