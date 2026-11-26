# Signed occurrences in Hilbert Specht sweeps

Fix a bijection between a Young diagram of size $n$ and $[n]$. Let $R_\lambda,C_\lambda$ be the subgroups preserving each row and each column respectively. In the finite Hilbert space $\ell^2(S_n;\mathbb C)$ with its counting inner product, take the vector $\sum_{c\in C_\lambda}\sum_{a\in R_\lambda}\operatorname{sgn}(c)\delta_{ca}$. Its left translates span $V_\lambda$ with the induced inner product and action $(g\cdot f)(h)=f(g^{-1}h)$.

For $u+v+l=n$, the consecutive-block inclusion of $S_u\times S_v\times S_l$ acts on $V_\lambda$. A signed occurrence of $(\alpha,\beta,\gamma)$ is an injective complex linear intertwiner from $(V_\alpha\otimes V_{\beta^\top})\otimes V_\gamma$ for this restriction; the middle transpose is part of the model. For $n=2^d$, relabel the underlying points by the $d$-cube via a bijection. At coordinate $i$, average the action uniformly over permutations preserving the fibers of all other coordinates. Compose these averages in chronological order, earliest operator acting first, to obtain $Q$. The weighted moment at natural $r$ is $\dim(V_\lambda)\operatorname{Re}\operatorname{tr}((Q^*Q)^r)$, with extended real log $-\infty$ at zero. This regular Hilbert realization is not silently replaced by the tabloid inner product.

## Sources

- [Pinned source definition](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SignedSweepMoment.lean#L11-L162)
