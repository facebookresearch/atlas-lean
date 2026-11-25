# The Ξ-coalescent rate matrix on partitions of a finite sample

Let $\Xi = a\,\delta_0 + \Xi_0$ be as in the definition of the [Ξ-merger rates](xi-coalescents-simultaneous-multiple-collisions.md) $\lambda_{b; k_1, \dots, k_r; s}$. For $n \ge 1$ define the matrix $Q^\Xi_n$ on the set $\mathcal P_n$ of
partitions of $\{1, \dots, n\}$: if $\pi$ has $b$ blocks and $\pi'$ is obtained from $\pi$ by merging $r \ge 1$ disjoint groups of $k_1, \dots, k_r \ge 2$ blocks, each
into one block, leaving $s = b - \sum_j k_j$ blocks unchanged, then $Q^\Xi_n(\pi, \pi') = \lambda_{b; k_1, \dots, k_r; s}$; all other off-diagonal entries are $0$, and the diagonal
makes the row sums $0$. Then:

1. $Q^\Xi_n$ is a rate matrix (each off-diagonal entry is finite and nonnegative);
2. it is exchangeable, $Q^\Xi_n(\sigma\pi, \sigma\pi') = Q^\Xi_n(\pi, \pi')$ for every permutation $\sigma$ of $\{1, \dots, n\}$, because the rates depend only on the group sizes;
3. it is lumpable along the number of blocks, since the total rate from $\pi$ into partitions with a given number of blocks depends only on the number $b$ of blocks of $\pi$;
4. it is consistent under restriction, $Q^\Xi_{n+1} R = R\, Q^\Xi_n$ for the restriction map $R$ from $\mathcal P_{n+1}$ to $\mathcal P_n$, which is the consistency relation of the rates read on partitions.

When $\Xi$ is concentrated on $\{\zeta_2 = \zeta_3 = \dots = 0\}$, $Q^\Xi_n$ is the [Λ-coalescent rate matrix](the-coalescent-rate-matrix-on-partitions-of-a-fi.md) $Q^\Lambda_n$.

## Depends on

- [Merger rates of a coalescent with simultaneous multiple collisions](xi-coalescents-simultaneous-multiple-collisions.md)

## Related topics

- [The Λ-coalescent rate matrix on partitions of a finite sample](the-coalescent-rate-matrix-on-partitions-of-a-fi.md)

## Sources

- M. Birkner, J. Blath, M. Möhle, M. Steinrücken and J. Tams, "A modified lookdown construction for the Xi-Fleming-Viot process with mutation and populations with recurrent bottlenecks", arXiv:0808.0412 (2008), Sections 1.3–1.4; J. Schweinsberg, "Coalescents with simultaneous multiple collisions", Electronic Journal of Probability 5 (2000).
