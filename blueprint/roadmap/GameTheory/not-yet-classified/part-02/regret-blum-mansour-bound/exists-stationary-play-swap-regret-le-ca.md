# Black-box reduction from swap to external regret

Let $q_t(j, \cdot)$ be probability distributions on a finite nonempty action set $K$ for every time $t$ and copy $j \in K$. Then there is a play $p_t$ of probability distributions that is stationary, $p_t(i) = \sum_j p_t(j)\,q_t(j, i)$ for all $t$ and $i$, such that if every copy $j$ has external regret at most $R$ against its scaled losses $p_t(j)\,\ell_t$, then the swap regret of $p$ against $\ell$ is at most $|K| R$.
