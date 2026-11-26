# Exact value-query count of submodular greedy

On a ground set of $n$ distinct elements with budget $k \le n$, the cardinality-constrained greedy algorithm makes exactly $\sum_{t=0}^{k-1} (n - t) \le kn$ value queries against every value oracle (one query per remaining candidate per round). With a matroid constraint and value and independence queries charged separately, the matroid greedy for submodular maximization makes at most $n(n+1)/2$ queries of each kind, and exactly one independence query per candidate per round.

## Depends on

- [Value and independence oracle models](value-and-independence-oracle-models.md)
- [Nemhauser-Wolsey-Fisher: greedy is a (1 - 1/e)-approximation under a cardinality constraint](nemhauser-wolsey-fisher-greedy.md)

## Sources

- G. L. Nemhauser, L. A. Wolsey and M. L. Fisher, "An Analysis of Approximations for Maximizing Submodular Set Functions I", Mathematical Programming 14, 1978.
- M. L. Fisher, G. L. Nemhauser and L. A. Wolsey, "An Analysis of Approximations for Maximizing Submodular Set Functions II", Mathematical Programming Study 8, 1978.
