# Value-oracle lower bounds for submodular maximization

Consider deterministic algorithms that, for budget $k = 1$, return a set of size at most $1$ whose value is at least $c$ times the optimum on every normalized ($f(\emptyset) = 0$) monotone submodular function on a ground set of $n$ elements. If $c > 1/2$, every such algorithm makes at least $n - 1$ value queries on some function; if $c > 100/159$, at least $n$ queries. In particular every deterministic $(1 - 1/e)$-approximate algorithm makes at least $n$ queries for $n \ge 2$, matching the $n$ queries of greedy at $k = 1$.

## Proof sketch

Adversary argument: answer every query consistently with a function in which all singletons look alike; an unqueried element can be made much more valuable than the returned one while keeping all answers and submodularity.

## Depends on

- [Value and independence oracle models](value-and-independence-oracle-models.md)

## Sources

- G. L. Nemhauser and L. A. Wolsey, "Best Algorithms for Approximating the Maximum of a Submodular Set Function", Mathematics of Operations Research 3(3), 1978.
