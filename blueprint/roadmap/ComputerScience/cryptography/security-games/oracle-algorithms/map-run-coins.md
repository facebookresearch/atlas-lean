# Presampling the oracle's coins

Let $R$ be a finite nonempty set of coins, $O : X \times R \to Y$, and $c$ an $n$-query-bounded oracle
computation with queries in $X$ and answers in $Y$: it asks at most $n$ queries along every path,
whatever the answers. Run on $n$ independent uniform coins, $c$ has the output distribution of its run
against the randomized oracle that answers each query $x$ with $O(x, \rho)$ for a fresh uniform
$\rho \in R$.
