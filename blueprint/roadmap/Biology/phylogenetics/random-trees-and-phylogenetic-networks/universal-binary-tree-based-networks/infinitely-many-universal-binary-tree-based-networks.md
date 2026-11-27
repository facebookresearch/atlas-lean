# Infinitely many universal binary tree-based networks

**Definitions.** A rooted binary phylogenetic network $\mathcal N$ on a leaf set $X$ with $|X|=n$ is *tree-based with base tree $\mathcal T$* if $\mathcal N$ is obtained from a subdivision $\mathcal T'$ of a rooted binary phylogenetic tree $\mathcal T$ on $X$ by adding a set $I$ of pairwise vertex-disjoint *linking arcs* between subdivision vertices (*attachment points*); equivalently, deleting the arcs of $I$ leaves a graph homeomorphic to $\mathcal T$. A tree-based network on $X$ is *universal* if every one of the $(2n-3)!!$ rooted binary phylogenetic trees on $X$ is a base tree of it, i.e. for each tree $\mathcal T^{(i)}$ there is a set $I^{(i)}$ of linking arcs whose deletion leaves a subdivision of $\mathcal T^{(i)}$.

**Theorem.** For every $n>1$ there are infinitely many universal tree-based networks on a set of $n$ leaves.

This answers in the affirmative the question of Francis and Steel, who had exhibited a universal tree-based network for $n=3$.

## Expansion

*Universal shapes.* Let $U_n$ be the unlabelled network obtained from the caterpillar shape on $n$ leaves by adding $(n-1)(n-2)/2$ linking arcs with $(n-1)(n-2)$ attachment points so that any two cherries of the caterpillar spine can be rewired. By induction, $U_n$ realizes every binary tree shape: a shape $T_{n+1}=T_n+T_1$ is obtained by deleting a set of vertex-disjoint arcs that splits $U_{n+1}$ into copies homeomorphic to $U_n$ and a single leaf, and a shape $T_{n+1}=T_k+T_{n-k+1}$ by deleting two disjoint arc sets that delineate copies of $U_k$ and $U_{n-k+1}$; universality of the smaller shapes finishes the induction ($U_2$ and $U_3$ are checked directly). The number of unlabelled rooted binary shapes satisfies Harding's recursion ($r_{2k-1}=\sum_{i<k}r_ir_{n-i}$, $r_{2k}=\tfrac{r_k(r_k+1)}{2}+\sum_{i<k}r_ir_{n-i}$), which is what the induction ranges over.

*Labels.* Label $U_n$ by a permutation $\pi_0$ of $X$. A *crossover* $\sigma_{ij}$ subdivides the terminal arcs of leaves $i$ and $j$ twice and adds two crossing linking arcs between them; choosing the crossing arcs as tree arcs swaps the labels $i$ and $j$. Since adjacent transpositions generate the symmetric group, adding a series of crossovers for each of the $n!-1$ other label permutations makes every labelled tree a base tree. Adding further redundant crossovers keeps universality and yields infinitely many distinct universal networks. The construction uses far more arcs than necessary; finding universal tree-based networks with the fewest arcs is left open.

## Sources

- Momoko Hayamizu, "On the existence of infinitely many universal tree-based networks", Journal of Theoretical Biology 396 (2016), 204–206, <https://doi.org/10.1016/j.jtbi.2016.02.023>. Published version of arXiv:1512.02402, cited next; locators there refer to the arXiv version.
- Momoko Hayamizu, "On the existence of infinitely many universal tree-based networks", arXiv:1512.02402 (2015): definitions in Section 2, Proposition 2.2 (Harding's recursion), Theorem 3.1 and its proof. <https://doi.org/10.48550/arXiv.1512.02402>
