# Poisson construction of the Λ-coalescent

Let $\Lambda$ be a finite measure on $[0, 1]$ with $\Lambda(\{0\}) = 0$, and let $(p_i, t_i)_{i \ge 1}$ be the points of a Poisson point process on $(0, 1] \times \mathbb{R}_+$ with intensity $p^{-2}\Lambda(dp) \otimes dt$. At each time $t_i$ perform a $p_i$-merger: every block present takes part independently with probability $p_i$, and the blocks that take part merge into one. Restricted to $\{1, \dots, n\}$ this is well defined, because only finitely many points change the restriction in a bounded time interval (two given integers merge at total rate $\int p^2 \cdot p^{-2}\Lambda(dp) = \Lambda([0, 1]) < \infty$); the restrictions are consistent, and the resulting process on partitions of $\mathbb{N}$ is the [$\Lambda$-coalescent](../multiple-merger-coalescents/speed-of-coming-down-from-infinity/lambda-coalescent-on-n-as-a-time-indexed-cadlag.md), whose $b$-block, $k$-merger rate is $\lambda_{b,k} = \int_0^1 p^{k-2}(1 - p)^{b-k}\Lambda(dp)$ (Berestycki 2009, Theorem 3.2 and Sec. 3.1). The target is this construction and its equality in law with the coalescent defined by the [merger-rate generator](the-coalescent-rate-matrix-on-partitions-of-a-fi.md).

## Depends on

- [Pitman's merger rate](../../../Biology/coalescent-theory/coalescents/merger-rate.md)
- [The Λ-coalescent rate matrix on partitions of a finite sample](the-coalescent-rate-matrix-on-partitions-of-a-fi.md)
- [The Λ-coalescent on the natural numbers](../multiple-merger-coalescents/speed-of-coming-down-from-infinity/lambda-coalescent-on-n-as-a-time-indexed-cadlag.md)

## Proof depends on

- [Pitman's consistency relation](../../../Biology/coalescent-theory/coalescents/merger-rate-consistent.md)

## Expansion

1. [Pitman's merger rates](../../../Biology/coalescent-theory/coalescents/merger-rate.md) and their [consistency relation](../../../Biology/coalescent-theory/coalescents/merger-rate-consistent.md).
2. The marked Poisson process restricted to $\{1, \dots, n\}$: finitely many effective points on bounded intervals, and the induced jump rates $\lambda_{b,k}$ for each set of $k$ of $b$ blocks.
3. Consistency of the restrictions and the process on partitions of $\mathbb{N}$.
4. Equality in law with the generator construction of the $\Lambda$-coalescent on $\mathbb{N}$.
5. A Kingman component $\Lambda(\{0\}) > 0$, added as independent pair mergers, as a separate statement.

## Sources

- Original result: J. Pitman, Coalescents with multiple collisions, Ann. Probab. 27 (1999), 1870–1902. <https://doi.org/10.1214/aop/1022874819> The construction follows Berestycki (2009), Theorem 3.2.
- N. Berestycki, *Recent Progress in Coalescent Theory*, Ensaios Matemáticos 16, Sociedade Brasileira de Matemática, 2009. <https://arxiv.org/abs/0909.3985>
