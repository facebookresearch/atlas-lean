# Shapley transformation of an unrooted phylogenetic tree and its failure to determine topology

Let $\mathcal{T}$ be an unrooted binary phylogenetic tree on leaf set $X = \{1, \dots, n\}$ with positive edge lengths, leaf edges $e_1, \dots, e_n$ and internal edges $I_1, \dots, I_{n-3}$. For $S \subseteq X$ let $PD(S)$ be the total length of the smallest subtree spanning $S$. The **phylogenetic tree game** is the cooperative game $(X, PD)$, and its Shapley value is

$$ SV_i = \frac{1}{n!} \sum_{S \subseteq X,\ i \in S} (|S|-1)!\,(n-|S|)!\,\bigl( PD(S) - PD(S \setminus \{i\}) \bigr). $$

Removing an edge $k$ splits the leaves into the part $\mathcal{C}(i,k)$ containing $i$ and the far part $\mathcal{F}(i,k)$; the **split counts** are $c(i,k) = |\mathcal{C}(i,k)|$ and $f(i,k) = |\mathcal{F}(i,k)| = n - c(i,k)$.

**Shapley transformation** (Haake, Kashiwada and Su). $SV = \mathbf{M} \vec E$, where $\vec E = (\alpha_{e_1}, \dots, \alpha_{e_n}, \alpha_{I_1}, \dots, \alpha_{I_{n-3}})^\top$ is the vector of edge lengths and $\mathbf{M}$ is the $n \times (2n-3)$ matrix

$$ \mathbf{M}[i,k] = \frac{f(i,k)}{n\, c(i,k)}. $$

Its null space has dimension $n-3$, with basis $\{w_{I_k}\}_{k=1}^{n-3}$, where $(w_{I_k})_i = -\frac{f(i,I_k) - 1}{(n-2)\, c(i,I_k)}$ for $1 \le i \le n$, $(w_{I_k})_{n+k} = 1$, and all other entries are $0$. Isomorphic trees give permutation-equivalent matrices and null spaces.

**Non-identifiability.** The converse fails: there are non-isomorphic trees whose Shapley transformation matrices, and whose null spaces, are permutation-equivalent. An explicit family on at least $16$ leaves is obtained by joining four rooted subtrees $\mathcal{T}_A, \mathcal{T}_B, \mathcal{T}_C, \mathcal{T}_D$ with $|A| = |B| \ge 4$, $|C| = |D| \ge 4$, where $\mathcal{T}_A, \mathcal{T}_B$ have different shapes and $\mathcal{T}_C, \mathcal{T}_D$ have different shapes, in two different arrangements that preserve every split count. Consequently, neither the split counts nor the Shapley values of all leaves suffice to reconstruct the tree topology.

## Expansion

Because $PD$ is a sum of edge lengths, the Shapley value is additive over edges: edge $k$ contributes $\alpha_k$ to the marginal value of leaf $i$ exactly when, in a uniformly random order of the players, $i$ precedes every other leaf of $\mathcal{C}(i,k)$ but follows at least one leaf of $\mathcal{F}(i,k)$. This has probability $\frac{1}{c(i,k)} - \frac{1}{n} = \frac{f(i,k)}{n\,c(i,k)}$. Every column of $\mathbf{M}$ sums to $1$ (the efficiency axiom), and the leaf-edge columns are nearly diagonal, so the $n$ leaf columns are independent and the kernel is spanned by one vector per internal edge, compensating its length by leaf lengths. The non-identifiability proof checks case by case (leaf and edge in the same subtree, in different subtrees, or edge on the central part) that the two arrangements have identical split counts, so $\mathbf{M}$ coincides up to permuting leaves and edges.

## Sources

- Claus-Jochen Haake, Akemi Kashiwada, Francis Edward Su, "The Shapley value of phylogenetic trees", Journal of Mathematical Biology 56 (2008), 479–497, <https://doi.org/10.1007/s00285-007-0126-2>. The Shapley transformation matrix, its null-space basis and the permutation equivalence for isomorphic trees.
- Kristina Wicke, Mareike Fischer, "On the Shapley Value of Unrooted Phylogenetic Trees", Bulletin of Mathematical Biology 81 (2019), 618–638, <https://doi.org/10.1007/s11538-018-0392-8>. Published version of arXiv:1707.09908, cited next; locators there refer to the arXiv version.
- Kristina Wicke, Mareike Fischer, "On the Shapley value of unrooted phylogenetic trees", arXiv (2017). Section 2 (phylogenetic tree game), Section 3 (Shapley transformation matrix, null-space basis, and the non-isomorphic pairs with permutation-equivalent matrices). <https://doi.org/10.48550/arXiv.1707.09908>
