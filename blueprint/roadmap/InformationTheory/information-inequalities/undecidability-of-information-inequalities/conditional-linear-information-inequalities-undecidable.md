# Conditional linear information inequalities are undecidable

No algorithm decides whether one linear inequality between the joint entropies of finitely many random variables follows from another; the same holds when either inequality is replaced by an equality.

For random variables $X_1, \dots, X_k$ with finite support let $\mathbf{h}(X_1, \dots, X_k) \in \mathbb{R}^{2^k - 1}$ be the vector of [joint entropies](../shearer-s-entropy-inequality/shearer-full-entropy.md) $H(X_{\mathcal{U}})$ of the subtuples $X_{\mathcal{U}}$, $\emptyset \ne \mathcal{U} \subseteq \{1, \dots, k\}$, each the [Shannon entropy](../../entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/shannon-entropy.md) of the joint distribution.

**Theorem (Li).** The following problem is undecidable: given $k \in \mathbb{Z}_{>0}$ and $\mathbf{a}, \mathbf{b} \in \mathbb{Q}^{2^k - 1}$, decide whether the implication

$$
\mathbf{a}^{\mathsf{T}} \mathbf{h}(X_1, \dots, X_k) \ge 0 \ \Longrightarrow\ \mathbf{b}^{\mathsf{T}} \mathbf{h}(X_1, \dots, X_k) \ge 0
$$

holds for all jointly distributed random variables $X_1, \dots, X_k$ with finite support. The problem remains undecidable if either or both of the two inequalities are replaced by equalities (Corollary 4 of the source).

The corollary also holds for discrete random variables with finite or countably infinite support and finite entropy. The source lists the decidability of unconditional linear information inequalities, $\mathbf{b}^{\mathsf{T}} \mathbf{h} \ge 0$ for all random variables, among the questions open before it, and its results do not settle it.

## Depends on

- [Joint entropy](../shearer-s-entropy-inequality/shearer-full-entropy.md)
- [Shannon entropy](../../entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/shannon-entropy.md)

## Proof depends on

- [Conditional independence implication is undecidable](conditional-independence-implication-is-undecidable.md)
- [Conditional mutual information in terms of entropies](../../entropy-and-mutual-information/conditional-mutual-information/finite-conditional-mutual-information-eq.md)
- [Nonnegativity of conditional mutual information](../../entropy-and-mutual-information/conditional-mutual-information/finite-conditional-mutual-information-no.md)
- [Vanishing conditional mutual information iff conditional independence](../../entropy-and-mutual-information/conditional-mutual-information/finite-conditional-mutual-information-eq-2.md)

## Expansion

A conditional independence statement $X_{\mathcal{U}} \perp X_{\mathcal{V}} \mid X_{\mathcal{W}}$ is the equation $I(X_{\mathcal{U}}; X_{\mathcal{V}} \mid X_{\mathcal{W}}) = 0$, a linear equation in the joint entropies. Since conditional mutual information is nonnegative, the conjunction of several such statements is equivalent to the single inequality $\sum_i I(X_{\mathcal{U}_i}; X_{\mathcal{V}_i} \mid X_{\mathcal{W}_i}) \le 0$, so the conditional independence implication problem reduces to the problem above. The source states this reduction in its introduction (conditional independence is the inequality $I(X;Y \mid Z) \le 0$); with $\mathbf{b}^{\mathsf{T}}\mathbf{h} = -I(X_{\mathcal{U}_0}; X_{\mathcal{V}_0} \mid X_{\mathcal{W}_0})$ the conclusion is the target statement, and the equality versions follow in the same way.

## Sources

- C. T. Li, "Undecidability of network coding, conditional information inequalities, and conditional independence implication", IEEE Transactions on Information Theory 69 (2023), no. 6, 3493–3510, https://doi.org/10.1109/TIT.2023.3247570; read in arXiv:2205.11461v3 (Corollary 4, its footnote and the introduction of arXiv:2205.11461v3).
