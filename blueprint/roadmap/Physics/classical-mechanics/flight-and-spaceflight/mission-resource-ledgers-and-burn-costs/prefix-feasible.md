# Prefix Feasible

Prefix feasibility over a horizon of `N` steps: for every resource `i` and every prefix
`t ≤ N` (the start `t = 0` and the end `t = N` included), the stock is at least the floor
`lo i` plus the reserve `r i` and at most the capacity `hi i`. The reserve is deducted once,
in this lower bound; it is not also a scheduled flow. Reserves are nonnegative (`NNReal`), so
feasibility never certifies a stock below the floor (`PrefixFeasible.lo_le_stock`).
