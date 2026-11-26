# Opt Val le add of scaled Opt

For $n$ items with natural weights $w$ and profits $p$, a capacity $W$ and $K \ge 1$, write $R(S) = \sum_{i \in S} \lfloor p_i / K \rfloor$, rounding each item separately. If $R(T) \le R(S)$ for every feasible $T$, then the optimum satisfies $\mathrm{OPT} \le P(S) + nK$. The theorem does not require $S$ to be feasible, nor $\mathrm{OPT}$ to exceed $P(S)$.
