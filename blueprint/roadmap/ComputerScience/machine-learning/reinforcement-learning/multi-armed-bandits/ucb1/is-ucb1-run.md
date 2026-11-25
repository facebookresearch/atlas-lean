# Run of UCB1 on reward stacks

`IsUCB1Run x A` says that the arm sequence `A`, which plays
arm `A t` after `t` plays, is a run of UCB1 (Auer, Cesa-Bianchi and Fischer, 2002, Figure 1) on
the reward stacks `x`, where the `m`-th play of arm `j` (counted from `0`) yields the reward
`x j m`. Its first `K` plays play each arm once, in any order, and every later play, made after
`t ≥ K` plays, plays an arm maximizing the UCB1 index `ucb1Index x t c`, where
`c k = #{u < t | A u = k}` is the number of plays of arm `k` so far. Ties may be broken in any
way.
