# Satisfiability of affine constraints on joint entropies is undecidable

No algorithm decides whether some discrete random variables with finite entropies have joint entropies satisfying a given finite system of affine inequalities, or of affine equations, with rational coefficients; equivalently, whether the entropic region meets a given polyhedron.

Entropies are in bits (logarithms to base $2$). A *discrete* random variable takes countably many values; for a discrete random tuple with distribution $p$ its entropy is $H = -\sum_x p(x) \log_2 p(x) \in [0, \infty]$, which for a finitely supported $p$ is the [Shannon entropy](../../entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/shannon-entropy.md) of $p$. For jointly distributed discrete random variables $U_1, \dots, U_l$ with finite entropies let $\mathbf{h}(U^l) \in \mathbb{R}^{2^l - 1}$ be the vector of their joint entropies $H(U_{\mathcal{S}})$, the entropies of the subtuples $U_{\mathcal{S}} = (U_s)_{s \in \mathcal{S}}$, $\emptyset \ne \mathcal{S} \subseteq \{1, \dots, l\}$, and let the *entropic region* $\Gamma^*_l \subseteq \mathbb{R}^{2^l - 1}$ be the set of these vectors over all discrete joint distributions with finite entropies.

**Theorem (Li).** It is undecidable, given $l, m \ge 0$, $\mathbf{A} \in \mathbb{Q}^{m \times (2^l - 1)}$ and $\mathbf{b} \in \mathbb{Q}^m$, whether there are jointly distributed discrete random variables $U_1, \dots, U_l$ with finite entropies such that $\mathbf{A}\,\mathbf{h}(U^l) \succeq \mathbf{b}$ coordinatewise; the same holds for the equation $\mathbf{A}\,\mathbf{h}(U^l) = \mathbf{b}$ (Theorem 1 of the source).

The source derives further undecidable problems: whether every $\mathbf{v} \in \Gamma^*_n$ satisfies $\mathbf{a}_1^{\mathsf{T}} \mathbf{v} > b_1 \vee \dots \vee \mathbf{a}_N^{\mathsf{T}} \mathbf{v} > b_N$ for given rational $\mathbf{a}_i, b_i$ (Corollary 8); whether some $\mathbf{v} \in \Gamma^*_n$ has $\mathbf{a}^{\mathsf{T}} \mathbf{v} = 0$ and $v_{\{1\}} = 1$ (Corollary 7); and whether every $\mathbf{v} \in \Gamma^*_n$ with $\mathbf{a}^{\mathsf{T}} \mathbf{v} \le 0$ and $v_{\{1\}} \le 1$ has $v_{\{1\}} = 0$ (Corollary 6), where $v_{\{1\}}$ is the entropy of the first variable. The constructions are explicit, so for consistent ZFC there are $\mathbf{A}$ and $\mathbf{b}$ for which ZFC proves neither that $\mathbf{A}\mathbf{v} = \mathbf{b}$ has a solution in $\Gamma^*_n$ nor that it has none. The later paper of the same author removes the constant terms: [conditional linear information inequalities are undecidable](conditional-linear-information-inequalities-undecidable.md) (IEEE Trans. Inform. Theory 69 (2023) 3493–3510).

## Depends on

- [Shannon entropy](../../entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/shannon-entropy.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Conditional mutual information of a finite joint law](../../entropy-and-mutual-information/conditional-mutual-information/finite-conditional-mutual-information.md)

## Expansion

The proof reduces from the periodic tiling problem, whether a finite set of Wang tiles tiles the plane periodically, which Gurevich and Koryakov proved undecidable. Affine constraints force three variables to be uniform with a common cardinality (via the condition of Zhang and Yeung with vanishing conditional entropies and pairwise mutual informations), encode a torus grid of that size, and constrain the tiles placed on it; the variables then exist exactly when the tile set admits a periodic tiling. Corollaries 6 and 7 reduce from [conditional independence with one uniform bit](conditional-independence-with-a-uniform-bit-undecidable.md), and Corollary 8 follows by negating Theorem 1. The variables the construction builds from a periodic tiling are finitely supported. A good expansion links pages for the undecidability of the periodic tiling problem (Gurevich and Koryakov) and for the torus-grid construction.

## Sources

- C. T. Li, "The undecidability of conditional affine information inequalities and conditional independence implication with a binary constraint", IEEE Transactions on Information Theory 68 (2022), no. 12, 7685–7701, https://doi.org/10.1109/TIT.2022.3190800; read in arXiv:2104.05634v4 (the introduction, the notations, Section II on the entropic region, Section III, Theorem 1 and its proof in Section IV, and Corollaries 6, 7 and 8 of arXiv:2104.05634v4).
