# Edit distance on node-labeled trees

Let $\mathcal{L}$ be a leaf set and $\Lambda$ a finite label set. A tree on $\mathcal{L}$ (internal nodes of degree at least 3, except a root of degree at least 2) is **labeled** if each internal node $x$ carries $\lambda(x) \in \Lambda$. The edit operations are:

- **contraction** of an internal edge $\{x,y\}$ with $\lambda(x) = \lambda(y)$, identifying $x$ and $y$;
- **extension** of a non-binary node $x$ along a subset $X$ of its children with $|X| \ge 2$, creating a new child $y$ of $x$ adopting $X$, with $\lambda(y) = \lambda(x)$;
- **flip** of a node $x$ to a label $\lambda' \ne \lambda(x)$.

For unlabeled trees (only the first two operations), the minimum edit length is the Robinson–Foulds distance; for unrooted trees it equals $|\mathcal{B}(T_1)\setminus\mathcal{B}(T_2)| + |\mathcal{B}(T_2)\setminus\mathcal{B}(T_1)|$ over nontrivial bipartitions, and for rooted trees it equals the clade symmetric difference, which coincides with the unrooted distance after attaching a dummy leaf at each root.

1. (Metric.) On labeled trees of a fixed type, the minimum length $\delta(T_1, T_2)$ of an edit sequence from $T_1$ to $T_2$ is a metric.
2. (Paired bad subtrees.) An edge is **bad** if its bipartition is not shared by the other tree. For each maximal subtree $S$ of $T$ whose internal edges are bad and whose terminal edges are good, the edges of $T'$ with the same terminal bipartitions span a unique subtree $S'$, which is a maximal bad subtree of $T'$.
3. (Non-mixed bad edges first.) If $e$ is a bad edge whose ends have equal labels and $T_c$ is $T$ with $e$ contracted, then $\delta(T_c, T') = \delta(T,T') - 1$.
4. (Upper bound.) If $T, T'$ have $n$ internal nodes each and $e, e'$ internal bad edges, then $\delta(T,T') \le e + e' + n$; for binary trees $e = e'$ and the bound $2e + n$ is tight.

Unlike the unlabeled case, an optimal labeled edit path may contract **good** edges, so optimal paths do not always decompose over pairs of maximal bad subtrees.

## Depends on

- [Robinson–Foulds distance](../../splits-compatibility-ultrametrics-and-upgma/rf-dist.md)

## Expansion

Every operation has an inverse of the same kind (contraction and extension undo each other, a flip is undone by a flip), so $\delta$ is symmetric; it is zero only on identical trees, and concatenating paths gives the triangle inequality. A non-mixed bad edge must be contracted by every optimal path at some point, and moving its contraction to the front, replaying the rest with the merged node standing for either endpoint, costs nothing. After these contractions every remaining bad subtree is **mixed** (adjacent internal nodes differ in label), which reduces the problem to contracting mixed trees to stars and extending back.

## Sources

- S. Briand, C. Dessimoz, N. El-Mabrouk, M. Lafond and G. Lobinska, "A generalized Robinson–Foulds distance for labeled trees", BMC Genomics 21 (Suppl 10) (2020), Definition 1 and Lemmas 1–5, <https://doi.org/10.1186/s12864-020-07011-0>, PMCID: PMC7677779.
