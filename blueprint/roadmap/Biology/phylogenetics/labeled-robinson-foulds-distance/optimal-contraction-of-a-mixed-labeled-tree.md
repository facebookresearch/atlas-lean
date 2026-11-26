# Optimal contraction of a mixed labeled tree

A labeled tree with two labels is **mixed** if every internal edge joins differently labeled nodes, so no edge can be contracted without first flipping an endpoint. Let $\mathrm{diam}(T)$ be the number of edges on a longest path of $T$, and assume $T$ has at least two terminal edges.

**Lemma.** The minimum number of flips in an optimal sequence of flips and contractions transforming a mixed tree $T$ into a star tree is

$$\varphi(T) = \left\lceil \frac{\mathrm{diam}(T)}{2} \right\rceil - 1,$$

and the number of contractions is the number of internal edges of $T$. A greedy procedure (Contract-Tree) that repeatedly flips the centre of the tree, the midpoint of a longest chain, and contracts its now monochromatic edges attains this optimum. If $\mathrm{diam}(T)$ is even there are two centres, so the label of the final star can be chosen.

**Theorem (2-approximation).** Contract every pair of maximal bad subtrees $S \subseteq T$, $S' \subseteq T'$ to stars with Contract-Tree, flip once if the two star labels differ, and extend back to $T'$. The number $d$ of operations used satisfies $d \le 2\,\delta(T,T')$, where $\delta$ is the labeled edit distance.

## Depends on

- [Edit distance on node-labeled trees](edit-distance-on-node-labeled-trees.md)

## Expansion

Minimizing flips is not the same as making all labels equal, which would take $\min\{\#\mathrm{Spe}, \#\mathrm{Dup}\}$ flips: one flip of a central node followed by contractions merges a whole neighbourhood into one node, reducing the eccentricity of the centre by one. Each round lowers the diameter by two, giving $\lceil \mathrm{diam}/2\rceil - 1$ rounds before a star remains. For the approximation, any optimal path must contract every bad edge and spend at least one flip or good-edge contraction per bad subtree, while the algorithm contracts only bad edges and uses at most the number of bad edges plus twice the number of bad subtrees in flips. Comparing the two-sided contraction (both trees to stars) with contract-then-extend costs at most one extra flip per subtree pair.

## Sources

- S. Briand, C. Dessimoz, N. El-Mabrouk, M. Lafond and G. Lobinska, "A generalized Robinson–Foulds distance for labeled trees", BMC Genomics 21 (Suppl 10) (2020), Lemmas 6–7 and Theorems 1–2, <https://doi.org/10.1186/s12864-020-07011-0>, PMCID: PMC7677779.
