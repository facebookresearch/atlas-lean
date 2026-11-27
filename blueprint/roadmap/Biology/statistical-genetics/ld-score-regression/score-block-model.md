# Score-level LD-block model

Let $\mu$ be a measure on $\Omega$, $z_1, \dots, z_M$ real functions on $\Omega$ (the scores of $M$
markers) and $K$ a natural number. A score-level LD-block model for $(z_j)$ with block size $K$
consists of an LD block $b(j) \in \mathbb{N}$ for every marker $j$ such that

- every block has at most $K$ markers: $\#\{k : b(k) = b(j)\} \leq K$ for every $j$;
- $z_j$ and $z_k$ are independent under $\mu$ whenever $b(j) \neq b(k)$;
- every $z_j$ has a finite fourth moment: $z_j \in L^4(\mu)$.

It extends the [LD-score model](model.md), which fixes only second moments of effects and noise.
