# Satisfiability of affine constraints on joint entropies is undecidable

No algorithm decides whether some finitely supported random variables have joint entropies satisfying a given finite system of affine inequalities, or of affine equations, with rational coefficients; equivalently, whether the entropic region meets a given polyhedron.

For random variables $U_1, \dots, U_l$ with finite support let $\mathbf{h}(U^l) \in \mathbb{R}^{2^l - 1}$ be the vector of their [joint entropies](../shearer-s-entropy-inequality/shearer-full-entropy.md) $H(U_{\mathcal{S}})$, $\emptyset \ne \mathcal{S} \subseteq \{1, \dots, l\}$, each the [Shannon entropy](../../entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/shannon-entropy.md) of the joint distribution, and let the *entropic region* $\Gamma^*_l \subseteq \mathbb{R}^{2^l - 1}$ be the set of all such vectors.

**Theorem (Li).** It is undecidable, given $l, m \ge 0$, $\mathbf{A} \in \mathbb{Q}^{m \times (2^l - 1)}$ and $\mathbf{b} \in \mathbb{Q}^m$, whether there are random variables $U_1, \dots, U_l$ with finite support such that $\mathbf{A}\,\mathbf{h}(U^l) \succeq \mathbf{b}$ coordinatewise; the same holds for the equation $\mathbf{A}\,\mathbf{h}(U^l) = \mathbf{b}$ (Theorem 1 of the source).

The source derives further undecidable problems: whether every $\mathbf{v} \in \Gamma^*_n$ satisfies $\mathbf{a}_1^{\mathsf{T}} \mathbf{v} > b_1 \vee \dots \vee \mathbf{a}_N^{\mathsf{T}} \mathbf{v} > b_N$ for given rational $\mathbf{a}_i, b_i$ (Corollary 8); whether some $\mathbf{v} \in \Gamma^*_n$ has $\mathbf{a}^{\mathsf{T}} \mathbf{v} = 0$ and $v_{\{1\}} = 1$ (Corollary 7); and whether every $\mathbf{v} \in \Gamma^*_n$ with $\mathbf{a}^{\mathsf{T}} \mathbf{v} \le 0$ and $v_{\{1\}} \le 1$ has $v_{\{1\}} = 0$ (Corollary 6), where $v_{\{1\}}$ is the entropy of the first variable. The constructions are explicit, so for consistent ZFC there are $\mathbf{A}$ and $\mathbf{b}$ for which ZFC proves neither that $\mathbf{A}\mathbf{v} = \mathbf{b}$ has a solution in $\Gamma^*_n$ nor that it has none. The later refereed paper of the same author removes the constant terms: [conditional linear information inequalities are undecidable](conditional-linear-information-inequalities-undecidable.md) (IEEE Trans. Inform. Theory 69 (2023) 3493–3510).

## Depends on

- [Joint entropy](../shearer-s-entropy-inequality/shearer-full-entropy.md)
- [Shannon entropy](../../entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/shannon-entropy.md)
- [Conditional mutual information of a finite joint law](../../entropy-and-mutual-information/conditional-mutual-information/finite-conditional-mutual-information.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces from the periodic tiling problem, whether a finite set of Wang tiles tiles the plane periodically, which Gurevich and Koryakov proved undecidable. Affine constraints force three variables to be uniform with a common cardinality (via the condition of Zhang and Yeung with vanishing conditional entropies and pairwise mutual informations), encode a torus grid of that size, and constrain the tiles placed on it; the variables then exist exactly when the tile set admits a periodic tiling. Corollaries 6 and 7 reduce from [conditional independence with one uniform bit](conditional-independence-with-a-uniform-bit-undecidable.md), and Corollary 8 follows by negating Theorem 1. The periodic tiling theorem and the grid construction have no pages.

## Sources

- C. T. Li, "The undecidability of conditional affine information inequalities and conditional independence implication with a binary constraint", IEEE Transactions on Information Theory 68 (2022), no. 12, 7685–7701, https://doi.org/10.1109/TIT.2022.3190800; read in arXiv:2104.05634v4 (the introduction, Theorem 1 and Section 3, and Corollaries 6, 7 and 8 of arXiv:2104.05634v4).
