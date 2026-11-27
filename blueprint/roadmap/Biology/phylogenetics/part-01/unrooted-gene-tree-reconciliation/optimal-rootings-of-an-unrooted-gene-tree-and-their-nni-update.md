# Optimal rootings of an unrooted gene tree and their NNI update

Let $S$ be a rooted binary species tree, $a + b$ the least common ancestor of nodes $a, b$, and $M$ the LCA mapping of a rooted binary gene tree $G$ into $S$ ($M(v) = M(w_1) + M(w_2)$ for children $w_1, w_2$). An internal node $v$ is a **duplication** if $M(v) \in \{M(w_1), M(w_2)\}$, and it induces $L(M(w_1), M(w_2))$ **losses**, the number of species-tree nodes strictly between the images skipped by the embedding. The **weighted mutation cost** is $\sigma = \sum_v \big(\alpha\,\mathrm{dup}(v) + \beta\, \mathrm{loss}(v)\big)$ with $\alpha, \beta > 0$; $\sigma_D$ and $\sigma_L$ are the minimum numbers of duplications and losses needed to embed $G$ in $S$.

For an unrooted binary gene tree $G$, rooting on edge $e$ gives $G_e$ and cost $\sigma_e$; let $\mathrm{Min}_G$ be the set of edges minimizing $\sigma_e$. Replace each edge $\{v,w\}$ by two arcs and label the arc $\langle v, w \rangle$ with the LCA image of the leaves on $v$'s side, so each internal node is the centre of a **star** of three incoming and three outgoing labelled arcs, falling into five types according to which labels equal the species-tree root $\top$.

**Theorem (optimal rootings).** If $|\mathrm{Min}_G| > 1$, then $\mathrm{Min}_G$ consists of all edges belonging to stars in which all outgoing and at least two incoming arcs are labelled $\top$; if $|\mathrm{Min}_G| = 1$, its edge is the unique symmetric edge lying in a star with exactly two outgoing $\top$ arcs or with all outgoing and exactly one incoming $\top$ arc. Hence $\mathrm{Min}_G$ and the minimal cost are computable in $O(\max(|G|, |S|))$ time.

**Theorem (NNI update).** A nearest-neighbour interchange $((T_1,T_2),(T_3,T_4)) \mapsto ((T_2,T_3),(T_1,T_4))$ around an edge changes only the labels of the centre edge. Given the labelled arc graph, $\mathrm{Min}_G$, the optimal cost and constant-time LCA queries, the new optimal edge set and cost after one NNI are obtained in constant time by a case analysis on how the centre edge relates to $\mathrm{Min}_G$; for instance, if the centre edge is optimal before and after, the cost changes by an explicit expression in the four subtree images $a_1,\dots,a_4$.

Consequently the minimum weighted mutation cost over all rootings of all trees in the $k$-NNI neighbourhood of $G$ (or over NNIs restricted to weak, short edges) is computed in time linear in the size of that neighbourhood plus $O(\max(|G|,|S|))$ preprocessing, which simultaneously roots the gene tree and corrects likely topological errors.

## Depends on

- [Is LCAReconciliation](../../../not-yet-classified/lcareconciliation/is-lcareconciliation.md)

## Expansion

Rooting moves the single root-mapped node; every arc label is an LCA of a fixed leaf set, so the duplication and loss contributions of all nodes except those near the root are independent of the root position. The star types encode where the root image $\top$ is first reached, and the optimal edges form either a connected plateau of stars with many $\top$ labels or a single symmetric edge. An NNI swaps two subtrees across one edge, leaving every other arc's leaf set and hence label unchanged, which is why updates are local.

## Sources

- P. Górecki and O. Eulenstein, "Algorithms: simultaneous error-correction and rooting for gene tree reconciliation and the gene duplication problem", BMC Bioinformatics 13 (Suppl 10) (2012), S14, unrooted reconciliation (M1)–(M2), Definition 1, Lemmas 1–7 and the error-correction algorithm, <https://doi.org/10.1186/1471-2105-13-s10-s14>, PMCID: PMC3382441.
