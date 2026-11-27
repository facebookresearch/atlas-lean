# Exact value-query count of submodular greedy

On a ground set of $n$ elements with budget $k \le n$, the cardinality-constrained greedy algorithm, which in each of its $k$ rounds queries the value of the current set extended by each remaining candidate and adds a best one, makes $O(kn)$ value queries against every value oracle. With a matroid constraint, the matroid greedy algorithm for submodular maximization, which in each round tests every remaining candidate for independence and adds a feasible candidate of largest marginal value, makes $O(n^2)$ value queries and $O(n^2)$ independence queries.

## Proof sketch

Round $t$ (counting from $0$) of the cardinality greedy has $n - t$ remaining candidates and queries each once, so it makes exactly $\sum_{t=0}^{k-1} (n - t) \le kn$ value queries. The matroid greedy runs at most $n$ rounds, and round $t$ makes one independence query and at most one value query for each of its at most $n - t$ remaining candidates, at most $\sum_{t=0}^{n-1} (n - t) = n(n+1)/2$ queries of each kind.

## Depends on

- [Value and independence oracle models](value-and-independence-oracle-models.md)
- [Nemhauser-Wolsey-Fisher: greedy is a (1 - 1/e)-approximation under a cardinality constraint](nemhauser-wolsey-fisher-greedy.md)

## Sources

- G. L. Nemhauser, L. A. Wolsey and M. L. Fisher, "An Analysis of Approximations for Maximizing Submodular Set Functions I", Mathematical Programming 14, 1978.
- M. L. Fisher, G. L. Nemhauser and L. A. Wolsey, "An Analysis of Approximations for Maximizing Submodular Set Functions II", Mathematical Programming Study 8, 1978.
- A. Badanidiyuru and J. Vondrák, "Fast Algorithms for Maximizing Submodular Functions", Proceedings of the Twenty-Fifth Annual ACM-SIAM Symposium on Discrete Algorithms (SODA), 2014, Sections 1 and 3.
- B. Mirzasoleiman, A. Badanidiyuru, A. Karbasi, J. Vondrák and A. Krause, "Lazier Than Lazy Greedy", Proceedings of the Twenty-Ninth AAAI Conference on Artificial Intelligence, 2015, Introduction.
