# Probe-prefix bound for open addressing

Let there be $m \ge 1$ slots and let $S$ be the set of occupied slots, with $n = |S|$. A probe sequence is a permutation $\pi$ of the slots. For every $k$, the number of permutations whose first $\min(k, m)$ probes $\pi(0), \dots, \pi(\min(k,m)-1)$ all lie in $S$ is at most $m!\,(n/m)^k$.
