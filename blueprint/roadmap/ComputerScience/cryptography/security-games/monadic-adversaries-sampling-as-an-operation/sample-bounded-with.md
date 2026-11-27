# Sampling bound with a condition on the output

Over a signature extended with the sampling operations of a family ([With Sample](with-sample.md)), let $\mathsf{cont}$ be a predicate on outputs and natural numbers. A computation $c$ satisfies the sampling bound with budget $s$ and condition $\mathsf{cont}$ when it satisfies the [two-phase cost bound](cost-bounded-with.md) in which exactly the sampling operations are costly:

- along every path of $c$ at most $s$ sampling steps occur, while oracle queries are free (they are counted separately by [Oracle Bounded With](oracle-bounded-with.md));
- at each output $x$, reached with $j$ sampling units unused, $\mathsf{cont}(x, j)$ holds.

In particular a computation that returns $x$ at once satisfies the bound if and only if $\mathsf{cont}(x, s)$. A count of sampling steps alone is therefore not enough: with the predicate constantly false, even a computation that immediately returns $x$ fails the bound, although it takes no samples.
