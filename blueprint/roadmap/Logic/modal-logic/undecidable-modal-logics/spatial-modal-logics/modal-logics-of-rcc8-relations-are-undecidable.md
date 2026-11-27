# Modal logics of RCC8 relations over Euclidean regions are undecidable

The modal logic of the eight topological RCC8 relations is undecidable over regular closed regions of any topological space, and over regular closed, convex or rectangular regions of $\mathbb{R}^n$ for every $n \geq 1$.

**Theorem (Lutz and Wolter).** Each of the following [modal logics of topological relations](modal-logics-of-topological-relations.md) is undecidable: $L_{\mathrm{RCC8}}(\mathcal{TOP})$, the logic of all full concrete region structures of regular closed sets; and, for every $n \geq 1$, $L_{\mathrm{RCC8}}(\mathbb{R}^n, \mathbb{R}^n_{\mathrm{reg}})$, $L_{\mathrm{RCC8}}(\mathbb{R}^n, \mathbb{R}^n_{\mathrm{conv}})$ and $L_{\mathrm{RCC8}}(\mathbb{R}^n, \mathbb{R}^n_{\mathrm{rect}})$.

These are cases of the general theorem of the source: $L_{\mathrm{RCC8}}(\mathcal{S})$ is undecidable for every class $\mathcal{S}$ of region structures containing some $\mathfrak{R}(\mathbb{R}^n, U)$ with $\mathbb{R}^n_{\mathrm{rect}} \subseteq U$, and more generally whenever $\mathcal{S}$ contains a "domino ready" structure; the same holds for the logics of substructures of these region structures, and the logics of finite region structures above $\mathfrak{R}(\mathbb{R}^n, \mathbb{R}^n_{\mathrm{rect}})$ are undecidable as well. Already for $n = 1$ this covers interval temporal logics, improving earlier undecidability results of Halpern and Shoham.

## Depends on

- [Modal logics of topological relations](modal-logics-of-topological-relations.md)

## Proof depends on

- [The tiling problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

The proof reduces the domino problem for the first quadrant of the plane to satisfiability. Given a domino system $(T, H, V)$, a formula $\varphi_{\mathcal{D}}$ uses the universal modality and nominals, both definable, to force a grid-like arrangement of regions encoding the quadrant, and the presence of all rectangles in $U$ guarantees that a model encoding a given tiling exists in $\mathfrak{R}(\mathbb{R}^n, U)$. Tile propositions are then constrained so that $H$- and $V$-neighbors match, and $\varphi_{\mathcal{D}}$ is satisfiable iff the system tiles the quadrant, so validity is undecidable.

## Sources

- C. Lutz and F. Wolter, "Modal logics of topological relations", *Logical Methods in Computer Science* 2(2), Paper 5, 2006, doi:10.2168/LMCS-2(2:5)2006; read as arXiv:cs/0605064v2, <https://arxiv.org/abs/cs/0605064v2>: the main theorem of Section 5 of arXiv:cs/0605064v2 (classes containing some $\mathfrak{R}(\mathbb{R}^n, U)$ with $\mathbb{R}^n_{\mathrm{rect}} \subseteq U$), its corollary listing the logics above, and the generalization to domino-ready structures; the undecidability theorem for finite region structures in Section 7.
