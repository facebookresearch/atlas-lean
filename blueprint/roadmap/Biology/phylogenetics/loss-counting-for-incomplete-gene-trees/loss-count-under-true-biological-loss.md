# Loss count of an incomplete gene tree under true biological loss

Use the notation of the standard loss count entry: $gt$ is a rooted binary gene tree with $L(gt) \subseteq L(ST)$, $M$ the LCA mapping and $F(u, S)$ the per-node loss term. Now a species missing from $gt$ is interpreted as a genome that has lost the gene (gene birth and death), and the losses are counted on the full species tree $ST$ rather than on $ST(gt)$. A clade of $ST$ is **missing** if it contains no species of $gt$; the maximal missing clades not below $M(r(gt))$ form the set $\mathrm{UMMC}(gt, ST)$ of **upper maximal missing clades**.

Let $L_{bd}(gt, ST)$ be the minimum number of losses without assuming the gene was present at the root of $ST$, and $L^*_{bd}(gt, ST)$ the minimum assuming it was. Theorem 2 (from Chauve et al. and Górecki and Tiuryn) says that the LCA mapping still minimizes duplications and losses under this interpretation, and the duplication nodes are exactly the $v$ with $M(v) \in \{M(l), M(r)\}$.

**Theorem 3.** For every $gt$, $ST$ with $L(gt) \subseteq L(ST)$,

$$L_{bd}(gt, ST) = \sum_{u \in V_{int}(gt)} F(u, ST), \qquad L^*_{bd}(gt, ST) = L_{bd}(gt, ST) + |\mathrm{UMMC}(gt, ST)|,$$

and both are computable in $O(n + n')$ time, where $ST$ has $n$ leaves and $gt$ has $n'$ leaves. If $M(r(gt)) \ne r(ST)$ then $|\mathrm{UMMC}(gt, ST)| = d(M(r(gt)), r(ST)) + 1$.

In general $L_{bd} \ne L_{std}$: for $gt = ((a,b),c)$ and $ST = ((a,(b,d)),c)$ one has $L_{std} = 0$ but $L_{bd} = 1$ (the gene was lost on the branch to $d$). The difference changes the optimal species tree: **Theorem 4** exhibits 14 gene trees for which the species tree minimizing $\sum L_{std}$ does not minimize $\sum L_{bd}$ (nor $\sum L^*_{bd}$).

## Depends on

- [Standard loss count of an incomplete gene tree under taxon sampling](standard-loss-count-under-taxon-sampling.md)

## Expansion

Gene birth happens once, so the loss-minimizing birth point is on the edge above $M(r(gt))$ (or above $r(ST)$ if $M(r(gt)) = r(ST)$). Evaluating $F$ on the unsuppressed tree $ST$ counts every species-tree branch below the birth point along which the gene lineage must be lost, including branches to missing species that the suppression in $ST(gt)$ hides. If the gene is forced to be present at the root, it must additionally be lost on each edge leaving the path from $r(ST)$ to $M(r(gt))$, one per upper maximal missing clade. Linear time follows from linear-time LCA mapping. Summing over gene trees gives species-tree objectives that the paper optimizes exactly by a minimum-weight clique formulation over subtree bipartitions (Theorem 11).

## Sources

- M. S. Bayzid, T. Warnow, "Gene tree parsimony for incomplete gene trees: addressing true biological loss", Algorithms for Molecular Biology 13:1 (2018), Theorems 2, 3, 4 and 11, <https://doi.org/10.1186/s13015-017-0120-1>, PMCID PMC5774205.