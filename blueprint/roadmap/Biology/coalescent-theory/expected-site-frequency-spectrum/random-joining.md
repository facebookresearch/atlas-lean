# Random-joining law on block-size lists

The **random-joining** law: `randomJoining m b ps` is the probability that `m` steps of
random joining started from the block-size list `b` visit the list of block-size lists `ps`
(starting with `b` itself). Each step merges a pair of blocks chosen uniformly among all
pairs; the process stops once fewer than two blocks remain.
