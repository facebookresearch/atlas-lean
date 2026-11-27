# Complexity, kernel and branching for agreement forests of caterpillars

**Setting.** An unrooted binary phylogenetic tree $T$ on a taxon set $X$ is a *caterpillar* if every internal vertex lies on a single path. For two unrooted trees $T,T'$ on $X$, an *agreement forest* is a partition of $X$ into blocks $B_1,\dots,B_k$ such that the subtrees $T|B_i$ and $T'|B_i$ are pairwise vertex-disjoint in each tree and $T|B_i=T'|B_i$ for every $i$. The unrooted maximum agreement forest problem (uMAF) asks for the minimum $k$. The minimum $k$ minus $1$ equals the tree bisection and reconnection (TBR) distance $d_{TBR}(T,T')$. A *common chain* is a sequence of taxa forming the same caterpillar-like path in both trees.

**Theorem.**

1. *(Chain preservation.)* For any set $K$ of taxon-disjoint common chains there is a maximum agreement forest that keeps every chain of length $\ge3$ in $K$ in a single block, and also every $2$-chain in $K$ that is pendant in $T$ or $T'$.
2. *(Hardness.)* uMAF is NP-complete, and moreover APX-complete, even when both input trees are caterpillars.
3. *(Kernel.)* For caterpillars, the common-chain and subtree reductions alone give a kernel with at most $7k$ taxa (ignoring additive constants), where $k$ is the size of a maximum agreement forest, $k=d_{TBR}(T,T')+1$, and this bound is tight up to an additive constant.
4. *(Branching.)* For caterpillars $T,T'$ on $X$ one can decide in $O^*(2.49^k)$ time whether they have an agreement forest with at most $k$ components.

## Proof sketch

Agreement forests measure topological discordance: $d_{TBR}$ is the minimum number of tree bisection and reconnection moves turning $T$ into $T'$, and it lower-bounds the reticulation needed to reconcile two gene trees. The hardness reduction shows that the general NP-hardness and APX-hardness do not come from complicated tree shapes. Caterpillars are already as hard as arbitrary trees, so hardness gadgets survive in the simplest topology. For general trees the same two reduction rules give a tight $15k$ kernel, while for caterpillars they already give $7k$, below the $11k$ and $9k$ kernels that need more complex rules for general trees. After the reductions every common chain has bounded length, and each forest component accounts for a bounded number of chains. The branching algorithm uses the linear order of the caterpillar to branch on a small number of conflicting quartets, which beats the $O^*(3^k)$ branching algorithm for general trees.

## Sources

- S. Kelk and R. Meuwese, "Agreement forests of caterpillar trees: Complexity, kernelization and branching", *Theoretical Computer Science* 1003 (2024), 114608, <https://doi.org/10.1016/j.tcs.2024.114608>. Preprint version: arXiv:2307.12176 (2023), Theorem 1 and Corollary 1 (chain preservation, from earlier work), Theorem 2 (NP-completeness on caterpillars), Theorem 3 (APX-completeness), Theorem 4 (tight $7k$ kernel), Theorem 5 ($O^*(2.49^k)$ branching), <https://doi.org/10.48550/arXiv.2307.12176>.
