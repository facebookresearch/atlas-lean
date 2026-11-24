# Cherry distribution of uniformly random unrooted binary trees

Let $C_n$ be the number of cherries (pairs of leaves adjacent to a common vertex) of an unrooted binary phylogenetic tree on $n \ge 4$ labelled leaves drawn uniformly from all $(2n - 5)!!$ such trees. McKenzie and Steel (2000, Theorem 4) state, for $k \ge 2$,
$$P[C_n = k] = \frac{n!\,(n-2)!\,(n-4)!\; 2^{n-2k}}{(n-2k)!\,(2n-4)!\,k!\,(k-2)!},$$
$E[C_n] = \frac{n(n-1)}{2(2n-5)}$ and $\mathrm{Var}[C_n] = \frac{n(n-1)(n-4)(n-5)}{2(2n-5)^2(2n-7)}$; they attribute the exact distribution to Hendy and Penny and the mean to Steel and Penny, and derive the variance from Steel's formula for the factorial moments. Their Corollary 5 gives $(C_n - n/4)/\sqrt{n/16} \to N(0, 1)$ in distribution, proved by realizing the uniform model (Section 4.3: each new leaf is attached to a uniformly chosen edge) as an extended Pólya urn with black, white and red balls for cherry pendant edges, other pendant edges and interior edges, and applying the urn central limit theorem of their Section 3.

## Depends on

- [The number of unrooted binary phylogenetic trees](../../../Combinatorics/elementary-enumeration/counting-binary-phylogenetic-trees/nat-card-unrooted-binary-tree.md)

## Expansion

1. The model: unrooted binary trees on $n$ labelled leaves, their count $(2n-5)!!$ (Section 2), and the uniform distribution as the result of attaching leaves to uniformly chosen edges (Section 4.3).
2. The exact distribution by counting trees with $k$ cherries (Theorem 4(a)).
3. The mean and variance (Theorem 4(b)), the variance from the second factorial moment.
4. The three-colour urn, its generating matrix with principal eigenvalue $2$ and left eigenvector $(1/4, 1/4, 1/2)$, and the resulting normal limit with mean $n/4$ and variance $n/16$ (Corollary 5).
5. The effect of rooting or unrooting on the cherry count, which changes it by at most one (Lemma 6), as a separate statement.

## Sources

- A. McKenzie and M. Steel, Distributions of cherries for two models of trees, Math. Biosci. 164 (2000), 81–92, Theorem 4, Corollary 5 and Sections 3, 4.3. <https://doi.org/10.1016/S0025-5564(99)00060-7>
