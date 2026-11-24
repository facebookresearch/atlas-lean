# Dust criterion for Λ-coalescents

For a $\Lambda$-coalescent on $\mathbb{N}$ with $\Lambda(\{0\}) = 0$, Pitman (1999; Berestycki 2009, Theorem 3.5) shows that the coalescent has dust — at every time $t > 0$ a positive fraction of the integers are still singletons, almost surely — if and only if $\int_0^1 x^{-1}\Lambda(dx) < \infty$; when the integral is infinite, almost surely the singletons have asymptotic frequency $0$ at all times $t > 0$. If $\Lambda(\{0\}) > 0$ (a Kingman component), there is no dust. In the dust case, in the Poisson construction of the coalescent (Berestycki 2009, Theorem 3.2: at the points $(p_i, t_i)$ of a Poisson process with intensity $p^{-2}\Lambda(dp)\,dt$ each block takes part in a merger independently with probability $p_i$), the frequency of singletons at time $t$ is the random variable $S_t = \prod_{t_i \le t}(1 - p_i)$, so $-\log S_t$ is a subordinator, and $E[S_t] = \exp(-t\int_0^1 x^{-1}\Lambda(dx))$.

## Expansion

1. Asymptotic frequencies of blocks of an exchangeable partition (Kingman's representation).
2. The rate at which a given integer leaves the singletons: $\int_0^1 x\cdot x^{-2}\Lambda(dx) = \int x^{-1}\Lambda(dx)$ from the Poisson construction (with infinite rate when the integral diverges).
3. The singleton frequency in the dust case: the product formula for $S_t$, its expectation, and the subordinator $-\log S_t$.
4. The no-dust case, including a Kingman atom at $0$.

## Sources

- Original result: J. Pitman, Coalescents with multiple collisions, Ann. Probab. 27 (1999), 1870–1902. <https://doi.org/10.1214/aop/1022874819> The criterion follows Berestycki (2009), Theorem 3.5.
- N. Berestycki, *Recent Progress in Coalescent Theory*, Ensaios Matemáticos 16, Sociedade Brasileira de Matemática, 2009. <https://arxiv.org/abs/0909.3985>
