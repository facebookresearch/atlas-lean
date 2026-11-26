# Low-rank feature maps for factorizable library scores

Let $\Sigma$ be a finite alphabet, $L_p + L_s = L$, $r = |\Sigma|^{\min(L_p, L_s)}$, and let $m \le r$ be a positive integer. If $m' \ge m$, then for every score $f : \Sigma^L \to \mathbb R$ that is not identically zero there are feature maps $\varphi_p : \Sigma^{L_p} \to \mathbb R^{m'}$ and $\varphi_s : \Sigma^{L_s} \to \mathbb R^{m'}$ with

$$\frac{\sum_{x \in \Sigma^{L_p}} \sum_{y \in \Sigma^{L_s}} \big(f(x \oplus y) - \varphi_p(x) \cdot \varphi_s(y)\big)^2}{\sum_{z \in \Sigma^L} f(z)^2} \le 1 - \frac{m}{r}$$

while for $m' < m$ there is a score $f$, for example one whose matrix has $r$ equal singular values, admitting no such feature maps. Thus $m'$-dimensional prefix and suffix features always capture at least a fraction $m'/r$ of the squared norm of any score, and no smaller dimension guarantees that fraction for all scores.

## Depends on

- [Reverse kernel trick for factorizable library scores](reverse-kernel-trick-for-factorizable-library-scores.md)

## Proof depends on

- [Eckart–Young, best-approximation form](../../../../Probability/linear-models-multivariate/principal-component-analysis/is-least-frobenius-sub-sq.md)
- [Squared Frobenius norm as the sum of squared singular values](../../../../LinearAlgebra/matrix-decompositions/singular-value-decomposition/singular-value-decomposition-theorem/sum-sq-singular-values-eq-sum-sq-norm-of.md)

## Proof sketch

Arrange $f$ as the matrix $F$ with rows indexed by prefixes and columns by suffixes, $F_{xy} = f(x \oplus y)$; its rank is at most $r$. A pair of $m'$-dimensional feature maps is exactly a factorisation $\Phi_p \Phi_s^\top$ of a matrix of rank at most $m'$, so by the Eckart–Young theorem the smallest achievable numerator is $\sum_{k > m'} \sigma_k^2$, where $\sigma_1 \ge \sigma_2 \ge \dots$ are the singular values of $F$, while the denominator is $\|F\|_F^2 = \sum_k \sigma_k^2$. The top $m'$ squared singular values are at least the average share, so the relative error is at most $1 - m'/r \le 1 - m/r$ when $m' \ge m$. Conversely, a score whose matrix has $r$ equal singular values (for example a permutation-like $F$) has relative error exactly $1 - m'/r > 1 - m/r$ when $m' < m$. The theorem guarantees existence but also shows that some scores need features of dimension comparable to $|\Sigma|^{\min(L_p,L_s)}$, which is why Dai et al. look for structured scores (Potts models) or learned compact features instead of exact factorisations.

## Sources

- Z. Dai et al., "Ultra-high-diversity factorizable libraries for efficient therapeutic discovery", Genome Research 32 (2022), 1787–1794, <https://doi.org/10.1101/gr.276593.122> (PMC9528983), Methods, Theorem 1 (proof in Supplemental Methods, section B).
- C. Eckart, G. Young, "The approximation of one matrix by another of lower rank", Psychometrika 1 (1936), 211–218, <https://doi.org/10.1007/BF02288367>.
