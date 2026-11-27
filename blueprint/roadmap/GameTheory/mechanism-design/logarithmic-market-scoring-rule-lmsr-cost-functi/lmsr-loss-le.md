# Worst-case loss of the LMSR market maker

For $n$ outcomes ($n \ge 1$), a liquidity parameter $b > 0$ and trades from $0$ to $q$, the market maker's loss $q_i - (C_b(q) - C_b(0))$ when outcome $i$ occurs is at most $b\log n$, where $C_b$ is the LMSR cost.

Since $C_b(0) = b\log n$, the bound is equivalent to $q_i \le C_b(q)$: the cost dominates every outstanding-share quantity.
