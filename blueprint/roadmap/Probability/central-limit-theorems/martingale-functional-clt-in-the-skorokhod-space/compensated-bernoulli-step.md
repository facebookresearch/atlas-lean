# Compensated Bernoulli counting process

For counting increments $\xi_i \in \{0, 1\}$ with success probability $p$ and counting process $N_k = \sum_{i<k} \xi_i$, the compensated Bernoulli counting process is the path $t \mapsto (N_{\lfloor nt\rfloor} - p\lfloor nt\rfloor)/\sqrt n$ in the Skorokhod space $D([0, 1])$: counts minus compensator, diffusively scaled. It is the normalized partial-sum step process of the centred increments $\xi_i - p$.
