# Total Value le add of scaled Opt

For a list of $n$ items with natural weights and values, a capacity and $K \ge 1$, write $R(S) = \sum_{i \in S} \lfloor p_i / K \rfloor$ for the scaled profit of a set $S$ of item positions, rounding each item separately (two items of profit $1$ with $K = 2$ have scaled profit $0 + 0$, not $\lfloor 2/2 \rfloor$). If $R(T) \le R(S)$ for every feasible $T$, as for a feasible set optimal for the scaled profits, then every feasible $T$ has true value $P(T) \le P(S) + nK$.
