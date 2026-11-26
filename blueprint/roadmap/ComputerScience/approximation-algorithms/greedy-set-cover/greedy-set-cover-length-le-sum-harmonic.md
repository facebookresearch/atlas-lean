# Potential bound for greedy set cover

Let $F$ be a list of finite sets, $U$ a finite set,
and $H(n) = 1 + \frac12 + \dots + \frac1n$ the $n$-th harmonic number. For every list $C^*$ of
members of $F$ that together cover $U$, the list of sets returned by the greedy set cover
algorithm on $F$ and $U$ has length at most $\sum_{S \in C^*} H(|S \cap U|)$, where the sum
runs over the list $C^*$ with repetitions.
