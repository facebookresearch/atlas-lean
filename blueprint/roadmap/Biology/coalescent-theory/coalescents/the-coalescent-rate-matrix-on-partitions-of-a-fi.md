# The Λ-coalescent rate matrix on partitions of a finite sample

Let $\Lambda$ be a finite measure on $[0, 1]$ and let
[$\lambda_{b,k} = \int_0^1 x^{k-2} (1 - x)^{b-k}\, \Lambda(dx)$](merger-rate.md), $2 \le k \le b$, be Pitman's merger rates. For
$n \ge 1$ define the matrix $Q^\Lambda_n$ on the set $\mathcal P_n$ of partitions of $\{1, \dots, n\}$ by
$Q^\Lambda_n(\pi, \pi') = \lambda_{b,k}$ if $\pi$ has $b$ blocks and $\pi'$ is obtained from $\pi$ by merging
exactly one set of $k \ge 2$ of its blocks into one block, $Q^\Lambda_n(\pi, \pi') = 0$ for every other
$\pi' \ne \pi$, and $Q^\Lambda_n(\pi, \pi) = -\sum_{\pi' \ne \pi} Q^\Lambda_n(\pi, \pi')$. Then:

1. $Q^\Lambda_n$ is a rate matrix;
2. it is lumpable along the number of blocks, with lumped generator the
   [block-counting generator](block-counting-generator.md) of the Λ-coalescent;
3. it is exchangeable: $Q^\Lambda_n(\sigma\pi, \sigma\pi') = Q^\Lambda_n(\pi, \pi')$ for every permutation $\sigma$
   of $\{1, \dots, n\}$;
4. it is consistent under restriction: if $R$ is the matrix of the map $\mathcal P_{n+1} \to \mathcal P_n$
   that restricts a partition to $\{1, \dots, n\}$, then $Q^\Lambda_{n+1} R = R\, Q^\Lambda_n$.

For $\Lambda = \delta_0$ only pairwise mergers occur, at rate $1$, and $Q^\Lambda_n$ is
[Kingman's partition rate matrix](../partition-valued-kingman-coalescent/partition-rate.md).

## Depends on

- [Pitman's merger rates](merger-rate.md)
- [Block-counting generator of a Λ-coalescent](block-counting-generator.md)
- [Restriction matrix](../partition-valued-kingman-coalescent/restrict-matrix.md)

## Proof depends on

- [Consistency of Pitman's merger rates](merger-rate-consistent.md)

## Expansion

A sound expansion proves (4) entrywise, in two cases for $\pi \in \mathcal P_{n+1}$. If $n + 1$ lies in a
block that meets $\{1, \dots, n\}$, then $\pi$ and its restriction have the same number $b$ of blocks, in
bijection, and each merger of $\pi$ restricts to the merger of the same blocks at the same rate
$\lambda_{b,k}$. If $\{n + 1\}$ is a block of $\pi$, then $\pi$ has $b + 1$ blocks when its restriction has $b$;
a given $k$-merger of the restriction arises from a $k$-merger of $\pi$ not involving $\{n + 1\}$, at rate
$\lambda_{b+1,k}$, or from the $(k+1)$-merger that also involves it, at rate $\lambda_{b+1,k+1}$, and these add
up to $\lambda_{b,k}$ by Pitman's consistency relation $\lambda_{b,k} = \lambda_{b+1,k} + \lambda_{b+1,k+1}$;
mergers of $\{n + 1\}$ with a single other block are invisible in the restriction.
For $\Lambda = \delta_0$ the identity (4) is
[the Kingman case](../partition-valued-kingman-coalescent/partition-rate-mul-restrict-matrix.md).

## Sources

- J. Pitman, "Coalescents with multiple collisions", Annals of Probability 27 (1999), 1870–1902, <https://doi.org/10.1214/aop/1022874819>.
- N. Berestycki, *Recent progress in coalescent theory*, Ensaios Matemáticos 16, Sociedade Brasileira de Matemática (2009), preprint <https://arxiv.org/abs/0909.3985>, Section 3.1, equation (52), Definitions 3.1 and 3.2 and Theorem 3.1.
