# Lower bound for quantum search

The hybrid argument of Bennett, Bernstein, Brassard and Vazirani: when the oracle marks an item $y$,
the final state of a $T$-query algorithm moves by at most twice the sum, over the queries, of the norm
of the part of the oracle-free state that queries $y$. Since these parts have total squared norm at
most one at each query, Cauchy–Schwarz gives $\sum_y \|\psi_T^y - \psi_T\|^2 \le 4T^2$, and an
algorithm that finds every one of $N$ items with probability at least $1/2$ needs $N \le 16T^2 + 4$,
that is $\Omega(\sqrt N)$ queries. Grover's algorithm attains this order.

- [BBBV lower bound in the standard query model](card-le-of-forall-success.md)
- [Phase oracle marking one item](marking-oracle.md)
- [Lower bound for quantum search (BBBV)](mul-card-le-of-forall-success.md)
- [Born rule for the query register](norm-query-proj-sq.md)
- [The oracle-free run preserves the norm](norm-query-run-id.md)
- [Hybrid argument](norm-query-run-sub-query-run-le.md)
- [Query projection](query-proj.md)
- [Run of a query algorithm](query-run.md)
- [Summed hybrid bound](sum-norm-query-run-sub-query-run-sq-le.md)

## Related topics

- [Bounded-error quantum polynomial time (BQP)](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/README.md): Bennett et al. use the bound to show that, relative to a random oracle, NP is not contained in BQTime$(o(2^{n/2}))$.
