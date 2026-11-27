# State Kernel

For an MDP $M$ and a matrix of action weights $\pi : S \to A \to \mathbb R$, the matrix on states `stateKernel M π s s' = ∑ a, π s a * M.prob s a s'`. When $M$ has stochastic transitions and $\pi$ is a stochastic policy (row-stochastic), it is row-stochastic: the transition matrix of the states under $\pi$.
