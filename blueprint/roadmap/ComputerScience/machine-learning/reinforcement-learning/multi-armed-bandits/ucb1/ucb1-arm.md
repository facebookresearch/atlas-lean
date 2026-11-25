# UCB1 with least-index tie-breaking

With at least one arm (`K ≥ 1`), the arm that UCB1
plays on the reward stacks `x` after `t` plays is arm `t` if `t < K`, and otherwise the least arm
maximizing the UCB1 index `ucb1Index x t c`, where `c k` is the number of plays of arm `k` so
far.
