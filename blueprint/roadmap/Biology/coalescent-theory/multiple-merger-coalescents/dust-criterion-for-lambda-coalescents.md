# Dust criterion for Λ-coalescents

For a $\Lambda$-coalescent on $\mathbb{N}$ with $\Lambda(\{0\}) = 0$ and $\Lambda(\{1\}) = 0$, Pitman (1999, Lemma 25; Berestycki 2009, Theorem 3.5) shows that the coalescent has dust (at every time $t > 0$ a positive fraction of the integers are still singletons, almost surely) if and only if $\int_0^1 x^{-1}\Lambda(dx) < \infty$; when the integral is infinite, almost surely the singletons have asymptotic frequency $0$ at all times $t > 0$. If $\Lambda(\{0\}) > 0$ (a Kingman component), there is no dust. The condition $\Lambda(\{1\}) = 0$ is needed for the positive-dust claim: if $\Lambda(\{1\}) > 0$, then at an exponential time $\tau$ of rate $\Lambda(\{1\})$ every block takes part in one merger, so for $\Lambda = \delta_1$, where the integral equals $1$, the singleton frequency at a fixed $t > 0$ is $0$ with probability $1 - e^{-t}$. In that case, when $\Lambda(\{0\}) = 0$ and $\int_0^1 x^{-1}\Lambda(dx) < \infty$, the singleton frequency is positive for $t < \tau$ and zero for $t \ge \tau$.

In the [Poisson construction](../../../Biology/coalescent-theory/coalescents/poisson-construction-of-lambda-coalescents.md) of the coalescent (Berestycki 2009, Theorem 3.2: at the points $(p_i, t_i)$ of a Poisson process with intensity $p^{-2}\Lambda(dp)\,dt$ each block takes part in a merger independently with probability $p_i$), when $\Lambda(\{0\}) = 0$ and $\int_0^1 x^{-1}\Lambda(dx) < \infty$, the frequency of singletons at time $t$ is the random variable $S_t = \prod_{t_i \le t}(1 - p_i)$ and $E[S_t] = \exp(-t\int_0^1 x^{-1}\Lambda(dx))$ (Pitman 1999, Proposition 26 and Eq. (37), proved from the Poisson construction; the product form is this page's reading of that construction). If moreover $\Lambda(\{1\}) = 0$, then $-\log S_t$ is a drift-free subordinator (Pitman 1999, Proposition 26); if $\Lambda(\{1\}) > 0$, it is a subordinator killed (sent to $+\infty$) at the time $\tau$ of the first point with $p_i = 1$, a case this page derives from the same construction.

## Depends on

- [Poisson construction of the Λ-coalescent](../../../Biology/coalescent-theory/coalescents/poisson-construction-of-lambda-coalescents.md)

## Expansion

1. Asymptotic frequencies of blocks of an exchangeable partition (Kingman's representation).
2. The rate at which a given integer leaves the singletons: $\int_0^1 x\cdot x^{-2}\Lambda(dx) = \int x^{-1}\Lambda(dx)$ from the Poisson construction (with infinite rate when the integral diverges).
3. The singleton frequency in the dust case: the product formula for $S_t$, its expectation, and the subordinator $-\log S_t$.
4. The no-dust case, including a Kingman atom at $0$.
5. An atom of $\Lambda$ at $1$: the merger of all blocks at an exponential time of rate $\Lambda(\{1\})$, positivity of the singleton frequency only before it, and the killed subordinator.

## Sources

- Original result: J. Pitman, Coalescents with multiple collisions, Ann. Probab. 27 (1999), 1870–1902. Lemma 25, Proposition 26 and Eq. (37). <https://doi.org/10.1214/aop/1022874819> The criterion is also Berestycki (2009), Theorem 3.5.
- N. Berestycki, *Recent Progress in Coalescent Theory*, Ensaios Matemáticos 16, Sociedade Brasileira de Matemática, 2009. <https://arxiv.org/abs/0909.3985>
