# Size of the TBR neighbourhood of an unrooted binary tree

Let $\mathcal T$ be an unrooted binary phylogenetic tree with leaf set of size $n\ge4$. A **tree bisection and reconnection (TBR)** operation deletes an edge, splitting $\mathcal T$ into two subtrees, and reconnects them by a new edge joining a point of an edge (or the vertex) of one subtree to a point of an edge of the other, suppressing degree-2 vertices. **SPR** is the special case in which the reconnection point of one subtree is its old attachment point, and **NNI** the further special case of moves across a single internal edge. The TBR neighbourhood $N_{\mathrm{TBR}}(\mathcal T)$ is the set of trees, other than $\mathcal T$, obtainable by one TBR operation. Define

$$\Gamma(\mathcal T)=\sum_{A|B}|A|\,|B|,$$

the sum over all non-trivial splits $A|B$ of $\mathcal T$ (a quantity closely related to the Wiener index).

**Theorem.** For every unrooted binary tree $\mathcal T$ on $n\ge4$ leaves:

1. Two distinct TBR operations producing the same tree must both be NNI operations.
2. The number of SPR operations is $4(n-2)(n-3)$, and $|N_{\mathrm{SPR}}(\mathcal T)|=2(n-3)(2n-7)$, independent of the shape of $\mathcal T$.
3. The number of TBR operations is $4\Gamma(\mathcal T)-4(n-2)(n-3)$, and

$$|N_{\mathrm{TBR}}(\mathcal T)|=4\,\Gamma(\mathcal T)-(4n-2)(n-3).$$

4. $|N_{\mathrm{TBR}}(\mathcal T)|$ is maximized exactly by the caterpillars, for which $|N_{\mathrm{TBR}}(\mathcal T)|=\tfrac23n^3-4n^2+\tfrac{16}3n+2$, and minimized exactly by the complete (maximally balanced) trees, for which $|N_{\mathrm{TBR}}(\mathcal T)|=4n^2\lfloor\log_2n\rfloor+O(n^2)$.

For $n=4$, $\Gamma=4$ and the formula gives the two alternative quartet topologies.

## Expansion

Count TBR operations edge by edge: removing an edge inducing the split $A|B$ leaves two subtrees whose numbers of possible attachment points grow linearly in $|A|$ and $|B|$, so the number of reconnections is a product whose sum over all edges is an affine expression in $\Gamma(\mathcal T)$ with coefficients depending only on $n$; reconnections that restore $\mathcal T$ are discarded. Distinct operations can produce the same tree only when both are NNIs (item 1), and each NNI neighbour is produced by a fixed number of operations, so subtracting the overcount gives the neighbourhood size. All shape dependence therefore lives in $\Gamma(\mathcal T)$, which is largest for caterpillars (splits of every size $2,\dots,n-2$) and smallest for complete trees (most splits cut off clusters of size a power of $2$).

## Sources

- Peter J. Humphries, Taoyang Wu, "On the neighbourhoods of trees", arXiv (2012). Lemma 3.1, Theorem 3.3, Corollary 3.4 (after Allen and Steel), Theorems 3.5 and 3.6, Corollary 4.2, Theorem 4.5, Corollary 4.8. <https://doi.org/10.48550/arXiv.1202.2203>. Published version: IEEE/ACM Transactions on Computational Biology and Bioinformatics 10(3) (2013), 721–728, <https://doi.org/10.1109/tcbb.2013.66>; locators above refer to the arXiv version.
