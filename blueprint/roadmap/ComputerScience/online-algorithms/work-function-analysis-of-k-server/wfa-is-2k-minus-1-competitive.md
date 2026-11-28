# The work function algorithm is $(2k-1)$-competitive

For every metric space and every $k \ge 1$, the work function algorithm for the $k$-server problem satisfies $\mathrm{cost}_{\mathrm{WFA}}(\sigma) \le (2k - 1)\,\mathrm{OPT}(\sigma) + c$ for every request sequence $\sigma$, with $c$ independent of $\sigma$. This is within a factor of two of the conjectured optimum $k$.

## Proof sketch

Combine the two lemmas: $\mathrm{cost}_{\mathrm{WFA}} \le \sum_t \mathrm{ext}_t - \mathrm{OPT}_T \le 2k\,\mathrm{OPT}_T - \mathrm{OPT}_T + c_1$.

## Depends on

- [The k-server problem](../paging-and-k-server/the-k-server-problem.md)
- [Work functions and the work function algorithm](../paging-and-k-server/work-functions-and-the-work-function-algorithm.md)

## Proof depends on

- [Online cost of the work function algorithm via extended costs](wfa-cost-via-extended-cost.md)
- [Total extended cost is at most $2k \cdot \mathrm{OPT}$](extended-cost-bound.md)

## Sources

- Elias Koutsoupias, Christos H. Papadimitriou, "On the k-Server Conjecture", Journal of the ACM 42(5) (1995).
