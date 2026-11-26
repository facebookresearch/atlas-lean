# Concordance-factor signatures of cycles in level-1 quartet networks

Let $N^+$ be a metric rooted level-1 network on $X$ under the network multispecies coalescent, and let $s = \{a, b, c, d\} \subseteq X$ with unrooted quartet network $Q_s^-$ and concordance factors $\mathrm{CF}_s \in \Delta^2$ as in [the quartet concordance factor page](quartet-concordance-factors-depend-only-on-the-unrooted-quartet-network.md). A cycle of $Q_s^-$ of size $k$ whose hybrid node has exactly $j$ of the four taxa below it is called a $k_j$-cycle.

- $s$ satisfies the **Cycle property** if the two smallest entries of $\mathrm{CF}_s$ are not equal (the concordance factors are not treelike).
- $s$ satisfies the **Big Cycle (BC) property** if all three entries of $\mathrm{CF}_s$ are different.

**Statement.**

1. In a level-1 quartet network there are no $k$-cycles with $k \ge 5$, at most one 4-cycle (and then no 3-cycle), and at most two 3-cycles. Cycles inducing $2_1$- or $2_3$-cycles in $Q_s^-$ do not affect $\mathrm{CF}_s$.
2. If $s$ satisfies the Cycle property, then $Q_s^-$ contains a $3_2$-cycle or a 4-cycle.
3. For generic numerical parameters (all edge lengths and inheritance probabilities outside a set of Lebesgue measure zero), $s$ satisfies the BC property if and only if $Q_s^-$ contains a 4-cycle.
4. If $s$ satisfies the Cycle property but, for generic parameters, not the BC property, then $Q_s^-$ contains a $3_2$-cycle.
5. If $s$ satisfies the BC property, so that $Q_s^-$ contains a 4-cycle with hybrid node $v$, then the smallest entry of $\mathrm{CF}_s$ is $\mathrm{CF}_{AC|BD}$ if and only if the $v$-blocks containing $a$ and $c$ are not adjacent in the cycle.

## Depends on

- [Quartet concordance factors depend only on the unrooted quartet network](quartet-concordance-factors-depend-only-on-the-unrooted-quartet-network.md)

## Proof depends on

- [Quartet concordance factors depend only on the unrooted quartet network](quartet-concordance-factors-depend-only-on-the-unrooted-quartet-network.md)
- [Network multispecies coalescent: the gene-tree probability kernel of a fixed network](network-multispecies-coalescent-fixed-network-ge.md)

## Expansion

Contracting $2_1$- and $2_3$-cycles leaves concordance factors unchanged, and $2_2$-, $3_1$- and 4-cycles act through explicit mixtures with weights $\gamma^2$, $(1-\gamma)^2$, $2\gamma(1-\gamma)$ or $\gamma$, $1-\gamma$ of the concordance factors of the networks obtained by deleting one hybrid edge. Without a $3_2$-cycle or a 4-cycle these mixtures stay on the treelike segments of the simplex, giving part 2. A 4-cycle mixes two incompatible displayed quartet trees, which for generic parameters separates all three entries, while a $3_2$-cycle never produces three distinct entries; together with part 2 this gives parts 3 and 4.

## Sources

- H. Baños, "Identifying species network features from gene tree quartets under the coalescent model", Bulletin of Mathematical Biology 81 (2019), <https://doi.org/10.1007/s11538-018-0485-4> (PMC6344282). Definitions 16–17, Lemmas 5 and 7–10, Propositions 6–11, Theorem 3 and Corollary 4.
