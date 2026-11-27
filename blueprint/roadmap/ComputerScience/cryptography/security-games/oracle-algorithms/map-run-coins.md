# Presampling the oracle's coins

Let $R$ be a finite nonempty set of coins, $O : X \times R \to Y$, and $c$ an $n$-query-bounded oracle computation with queries in $X$ and answers in $Y$: it asks at most $n$ queries along every path, whatever the answers. Run on $n$ independent uniform coins, $c$ has the output distribution of its run against the randomized oracle that answers each query $x$ with $O(x, \rho)$ for a fresh uniform $\rho \in R$.

Equivalently, the output distribution against that randomized oracle equals the law of the result of running $c$ on a uniform tape $\rho \in R^n$, answering the $i$-th query $x$ with $O(x, \rho_i)$ and returning the output (the arbitrary default output is used only if another query is made after the last entry; the bound rules that out).
