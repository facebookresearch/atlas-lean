# UCB1 index

The index of arm `j` after `t` plays, when each arm `k` has been played `c k`
times and the `m`-th play of arm `k` (counted from `0`) gave the reward `x k m`, is the empirical
mean `(x j 0 + ⋯ + x j (c j - 1)) / c j` of arm `j` plus the exploration bonus
`√(2 ln t / c j)`. For `c j = 0` it is `0`, by Lean's conventions `x / 0 = 0` and `√0 = 0`; a run of
UCB1 uses the index only once every arm has been played.
