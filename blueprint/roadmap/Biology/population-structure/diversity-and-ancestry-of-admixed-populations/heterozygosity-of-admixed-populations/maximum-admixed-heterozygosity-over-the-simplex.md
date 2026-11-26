# Maximum heterozygosity of an admixed population over the admixture simplex

In the setting of [admixed heterozygosity](admixed-heterozygosity-decomposition-and-lower-bound.md), let $P$ be the $J \times K$ matrix of source allele frequencies, assume $P$ has rank $K$ (no source is a linear combination of the others, so $J \ge K$), and let $A = \mathbf 1\mathbf 1^\top - P^\top P$, so that $H_{\mathrm{adm}}(\gamma) = \gamma^\top A\gamma$ on $\Delta^{K-1}$.

**Theorem 5.** Suppose $\mathbf 1^\top (P^\top P)^{-1}\mathbf 1 \ne 1$ and that

$$\gamma^* = \frac{A^{-1}\mathbf 1}{\mathbf 1^\top A^{-1}\mathbf 1} = \frac{(P^\top P)^{-1}\mathbf 1}{\mathbf 1^\top (P^\top P)^{-1}\mathbf 1}$$

lies in $\Delta^{K-1}$. Then $H_{\mathrm{adm}}$ is maximized over $\Delta^{K-1}$ at $\gamma^*$, with maximum

$$H_{\mathrm{adm}}(\gamma^*) = \frac{1}{\mathbf 1^\top A^{-1}\mathbf 1} = 1 - \frac{1}{\mathbf 1^\top (P^\top P)^{-1}\mathbf 1}.$$

If $\gamma^* \notin \Delta^{K-1}$, the maximizer lies on the boundary of the simplex.

**Corollary 6 (face reduction).** Suppose $\mathbf 1^\top (P_S^\top P_S)^{-1}\mathbf 1 \ne 1$ for every nonempty $S \subseteq \{1, \dots, K\}$, where $P_S$ keeps the columns in $S$. Then the maximizer has support on some nonempty $S^*$, and its nonzero entries are $A_{S^*}^{-1}\mathbf 1 / (\mathbf 1^\top A_{S^*}^{-1}\mathbf 1)$ with $A_{S^*}$ the corresponding principal submatrix of $A$. Singleton supports give the vertices, where $H_{\mathrm{adm}} = H_k$.

**Proposition 4 (exceeding the most diverse source).** For every $K \ge 2$ there are source frequencies $P$ and fractions $\gamma$ with $H_{\mathrm{adm}}(\gamma) > \max_k H_k$. There are also source frequencies $P$ for which no $\gamma$ achieves this.

## Depends on

- [Heterozygosity of an admixed population and its lower bound](admixed-heterozygosity-decomposition-and-lower-bound.md)

## Expansion

Maximize $\gamma^\top A\gamma$ subject to $\mathbf 1^\top\gamma = 1$ with a Lagrange multiplier: $2A\gamma = \lambda\mathbf 1$ gives $\gamma \propto A^{-1}\mathbf 1$, and the constraint fixes the scale. Sherman–Morrison applied to $A = \mathbf 1\mathbf 1^\top - P^\top P$ shows that $A$ is invertible exactly when $\mathbf 1^\top(P^\top P)^{-1}\mathbf 1 \ne 1$ and that $A^{-1}\mathbf 1$ is proportional to $(P^\top P)^{-1}\mathbf 1$. Lemma 12 checks with the bordered Hessian $\begin{pmatrix}0 & \mathbf 1^\top\\ \mathbf 1 & 2A\end{pmatrix}$ that the critical point is a constrained local maximum. On the hyperplane $\mathbf 1^\top\gamma = 1$, $H_{\mathrm{adm}} = 1 - \|P\gamma\|^2$ is strictly concave because $P$ has full column rank, so the local maximum is global. When $\gamma^*$ falls outside the simplex, set the coordinate of one face to zero and recurse; this is Corollary 6.

## Sources

- S. M. Boca, L. Huang and N. A. Rosenberg, "On the heterozygosity of an admixed population", *Journal of Mathematical Biology* 81 (2020), 1217–1250, <https://doi.org/10.1007/s00285-020-01531-9> (PMC7710588), Section 3 (Proposition 4, Theorem 5, Corollary 6) and Appendix 1 (Lemma 12 and the proofs of Theorem 5 and Corollary 6).
