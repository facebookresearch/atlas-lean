# Compensated Bernoulli counting process

For real increments $\xi_i$, a real $p$ and partial sums $N_k = \sum_{i<k} \xi_i$, the compensated counting process is the path in the Skorokhod space $D([0, 1])$ given for $n > 0$ by $t \mapsto (N_{\lfloor nt\rfloor} - p\lfloor nt\rfloor)/\sqrt n$, and the zero path for $n = 0$. It is the normalized partial-sum step process of the centred increments $\xi_i - p$; no condition on the $\xi_i$ or on $p$ is imposed.

When $p \in [0, 1]$ and the increments take values in $\{0, 1\}$ with conditional success probability $p$ given the past (for instance, independent $\mathrm{Bernoulli}(p)$ increments), $p\lfloor nt\rfloor$ is the compensator of the count and the path is the diffusively scaled compensated Bernoulli counting process. A marginal success probability is not enough: if every increment equals one fair bit $B$, each has success probability $\tfrac12$, but the centred count is not a martingale.
