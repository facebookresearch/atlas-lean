# Q-factor factorization over bidirected-separated blocks

Let $b$ be a Bayesian network over a finite nonempty alphabet with latent nodes $L$. For a set $S$ of observed nodes let $Q[S](v)$ be the probability of the values of $v$ on $S$ after intervening to set every observed node outside $S$ to its value in $v$, latent nodes not intervened on. Let a set $H$ of observed nodes be partitioned into pairwise disjoint blocks $T$ such that no bidirected edge of the latent projection joins two different blocks. Then $Q[H](v) = \prod_T Q[T](v)$.
